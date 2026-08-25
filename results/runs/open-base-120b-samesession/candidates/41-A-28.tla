---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES clk, suspicion, timeout, last, outbox

(* ---------------------------------------------------------------------- *)
(* Helper definitions *)

SendCond(p) == (clk[p] % SendPoint = 0) /\ (clk[p] % PredictPoint # 0)

PredictCond(p) == (clk[p] % PredictPoint = 0) /\ (clk[p] % SendPoint # 0)

RecMsgs(p) == { m \in Messages :
                 m.to = p /\ m.type = "Alive" }

MaxThreshold(p) ==
  Max( { timeout[p][q] : q \in Proc } \cup { SendPoint , PredictPoint } )

(* ---------------------------------------------------------------------- *)
(* Initial state *)

Init ==
  /\ clk      = [p \in Proc |-> 0]
  /\ suspicion = [p \in Proc |-> {}]
  /\ timeout   = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ last      = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ outbox    = [p \in Proc |-> {}]

(* ---------------------------------------------------------------------- *)
(* Type invariant *)

TypeOK ==
  /\ clk      \in [Proc -> Nat]
  /\ suspicion \in [Proc -> SUBSET Proc]
  /\ timeout   \in [Proc -> [Proc -> Nat]]
  /\ last      \in [Proc -> [Proc -> Nat]]
  /\ outbox    \in [Proc -> SUBSET Messages]

(* ---------------------------------------------------------------------- *)
(* Actions *)

SendAlive(p) ==
  /\ SendCond(p)
  /\ outbox' = [outbox EXCEPT ![p] = 
                  { m \in Messages :
                      m.type = "Alive" /\ m.from = p /\ m.to \in Proc \ {p} }]
  /\ clk'    = [clk EXCEPT ![p] = clk[p] + 1]
  /\ last'   = [last EXCEPT ![p][q] = IF q # p THEN last[p][q] + 1 ELSE last[p][q]
                 FOR q \in Proc]
  /\ UNCHANGED << suspicion, timeout >>

Predict(p) ==
  /\ PredictCond(p)
  /\ suspicion' = [suspicion EXCEPT ![p] = 
                     suspicion[p] \cup 
                     { q \in Proc : q # p /\ last[p][q] > timeout[p][q] }]
  /\ last'      = [last EXCEPT ![p][q] = last[p][q] + 1 FOR q \in Proc]
  /\ clk'       = [clk EXCEPT ![p] = clk[p] + 1]
  /\ UNCHANGED << timeout, outbox >>

Receive(p) ==
  /\ ~SendCond(p) /\ ~PredictCond(p)
  /\ \E rec \subseteq RecMsgs(p) :
        LET senders == { m.from : m \in rec } IN
        /\ last'      = [last EXCEPT ![p][q] = 
                           IF q \in senders THEN 0
                           ELSE last[p][q] + 1
                           FOR q \in Proc]
        /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ setminus senders]
        /\ timeout'   = [timeout EXCEPT ![p][q] = 
                           IF q \in (suspicion[p] \cap senders) THEN timeout[p][q] + 1
                           ELSE timeout[p][q]
                           FOR q \in Proc]
        /\ clk'       = [clk EXCEPT ![p] = clk[p] + 1]
        /\ outbox'    = outbox

ResetClock(p) ==
  /\ clk[p] > MaxThreshold(p)
  /\ clk' = [clk EXCEPT ![p] = 0]
  /\ UNCHANGED << suspicion, timeout, last, outbox >>

(* ---------------------------------------------------------------------- *)
(* Next-state relation *)

Next ==
  \/ \E p \in Proc : SendAlive(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc : Receive(p)
  \/ \E p \in Proc : ResetClock(p)

vars == << clk, suspicion, timeout, last, outbox >>

(* ---------------------------------------------------------------------- *)
(* Specification *)

SPECIFICATION == Init /\ [][Next]_vars

INVARIANTS == TypeOK

PROPERTIES == TRUE

====