---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

(* ----------------------------------------------------------------------
   Types
   ---------------------------------------------------------------------- *)

Msg == [src : Proc, dst : Proc, kind : {"alive"}]

(* ----------------------------------------------------------------------
   Variables
   ---------------------------------------------------------------------- *)

VARIABLES suspect, timeout, lastHeard, clock, outMsgs

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)

Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ outMsgs = {}

(* ----------------------------------------------------------------------
   Actions
   ---------------------------------------------------------------------- *)

SendAlive(p) ==
    /\ clock[p] = SendPoint
    /\ clock[p] # PredictPoint
    /\ outMsgs' = outMsgs \cup { [src |-> p, dst |-> q, kind |-> "alive"] : q \in Proc \ {p} }
    /\ clock'   = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] =
                IF q \in suspect[p] THEN @ ELSE @ + 1 | q \in Proc]
    /\ UNCHANGED << suspect, timeout >>

Predict(p) ==
    /\ clock[p] = PredictPoint
    /\ clock[p] # SendPoint
    /\ newSuspect = suspect[p] \cup { q \in Proc \ {p} : lastHeard[p][q] > timeout[p][q] }
    /\ suspect' = [suspect EXCEPT ![p] = newSuspect]
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] = @ + 1 | q \in Proc]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ UNCHANGED << timeout, outMsgs >>

Receive(p) ==
    /\ clock[p] # SendPoint /\ clock[p] # PredictPoint
    /\ msgs = { m \in outMsgs : m.dst = p }
    /\ IF msgs = {} THEN
           /\ clock'   = [clock EXCEPT ![p] = @ + 1]
           /\ UNCHANGED << suspect, timeout, lastHeard, outMsgs >>
       ELSE
           /\ newSuspect = suspect[p] \ { m.src : m \in msgs }
           /\ newTimeout = [q \in Proc |-> IF q \in { m.src : m \in msgs }
                                            THEN timeout[p][q] + 1
                                            ELSE timeout[p][q] ]
           /\ suspect'  = [suspect EXCEPT ![p] = newSuspect]
           /\ timeout'  = [timeout EXCEPT ![p] = newTimeout]
           /\ lastHeard' = [lastHeard EXCEPT ![p][q] =
                    IF q \in { m.src : m \in msgs } THEN 0 ELSE @ : m \in msgs]
           /\ clock' = [clock EXCEPT ![p] = @ + 1]
           /\ outMsgs' = outMsgs \ msgs
           /\ UNCHANGED << >>

Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<suspect, timeout, lastHeard, clock, outMsgs>>

(* ----------------------------------------------------------------------
   Type invariant
   ---------------------------------------------------------------------- *)

TypeOK ==
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ \A p \in Proc : suspect[p] \subseteq Proc \ {p}
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock \in [Proc -> Nat]
    /\ outMsgs \in SUBSET Msg
    /\ \A p,q \in Proc : lastHeard[p][q] \in Nat
    /\ \A p,q \in Proc : timeout[p][q] \in Nat

====