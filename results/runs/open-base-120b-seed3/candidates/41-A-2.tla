---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, TLC

(*-----------------------------------------------------------------
  CONSTANTS
-----------------------------------------------------------------*)
CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

(*-----------------------------------------------------------------
  VARIABLES
-----------------------------------------------------------------*)
VARIABLES clock, timeout, last, suspicion, outbox, chan

vars == << clock, timeout, last, suspicion, outbox, chan >>

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
Message == [type : {"Alive"}, src : Proc, dst : Proc]

(* Set of all possible alive messages *)
AllMessages == { [type |-> "Alive", src |-> p, dst |-> q] :
                  p \in Proc, q \in Proc \ {p} }

(* Adaptive timeout limit for a process p *)
Limit(p) ==
  Max( {SendPoint, PredictPoint}
       \cup { timeout[p][q] : q \in Proc \ {p} } )

(*-----------------------------------------------------------------
  Initialization
-----------------------------------------------------------------*)
Init ==
  /\ clock = [p \in Proc |-> 0]
  /\ timeout = [p \in Proc |-> [q \in Proc \ {p} |-> d0]]
  /\ last = [p \in Proc |-> [q \in Proc \ {p} |-> 0]]
  /\ suspicion = [p \in Proc |-> {}]
  /\ outbox = [p \in Proc |-> {}]
  /\ chan = {}

(* Alias required by the configuration file *)
Init == Init
INIT == Init

(*-----------------------------------------------------------------
  Type invariant
-----------------------------------------------------------------*)
TypeOK ==
  /\ clock \in [Proc -> Nat]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ last \in [Proc -> [Proc -> Nat]]
  /\ suspicion \in [Proc -> SUBSET Proc]
  /\ outbox \in [Proc -> SUBSET Messages]
  /\ chan \in SUBSET Messages
  /\ \A p \in Proc :
        /\ outbox[p] \subseteq Messages
        /\ \A q \in Proc :
              (q # p) => last[p][q] \in Nat

INVARIANTS == TypeOK

(*-----------------------------------------------------------------
  Actions
-----------------------------------------------------------------*)
SendCond(p) == (clock[p] % SendPoint = 0) /\ (clock[p] % PredictPoint # 0)
PredictCond(p) == (clock[p] % PredictPoint = 0) /\ (clock[p] % SendPoint # 0)

Send(p) ==
  LET newMsgs == { [type |-> "Alive", src |-> p, dst |-> q] :
                     q \in Proc \ {p} } IN
  /\ SendCond(p)
  /\ outbox' = [outbox EXCEPT ![p] = newMsgs]
  /\ chan' = chan \cup newMsgs
  /\ last' = [last EXCEPT ![p] =
                [last[p] EXCEPT ![q] =
                  IF last[p][q] < timeout[p][q] THEN last[p][q] + 1
                  ELSE last[p][q] ] ] ]
  /\ suspicion' = suspicion
  /\ timeout' = timeout
  /\ clock' = [clock EXCEPT ![p] =
                IF clock[p] >= Limit(p) THEN 0 ELSE clock[p] + 1]

Predict(p) ==
  LET addSet == { q \in Proc \ {p} : last[p][q] > timeout[p][q] } IN
  /\ PredictCond(p)
  /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup addSet]
  /\ last' = [last EXCEPT ![p] =
                [last[p] EXCEPT ![q] =
                  IF last[p][q] < timeout[p][q] THEN last[p][q] + 1
                  ELSE last[p][q] ] ] ]
  /\ outbox' = outbox
  /\ chan' = chan
  /\ timeout' = timeout
  /\ clock' = [clock EXCEPT ![p] =
                IF clock[p] >= Limit(p) THEN 0 ELSE clock[p] + 1]

Receive(p) ==
  /\ ~SendCond(p) /\ ~PredictCond(p)
  LET msgs   == { m \in chan : m.dst = p /\ m.type = "Alive" }
      srcs   == { m.src : m \in msgs } IN
  /\ chan' = chan \ msgs
  /\ outbox' = outbox
  /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ srcs]
  /\ timeout' = [timeout EXCEPT ![p] =
                  [timeout[p] EXCEPT ![q] =
                    IF q \in srcs /\ q \in suspicion[p] THEN timeout[p][q] + 1
                    ELSE timeout[p][q] ] ] ]
  /\ last' = [last EXCEPT ![p] =
                [last[p] EXCEPT ![q] =
                  IF q \in srcs THEN 0
                  ELSE IF last[p][q] < timeout[p][q] THEN last[p][q] + 1
                  ELSE last[p][q] ] ] ]
  /\ clock' = [clock EXCEPT ![p] =
                IF clock[p] >= Limit(p) THEN 0 ELSE clock[p] + 1]

(*-----------------------------------------------------------------
  Next-state relation
-----------------------------------------------------------------*)
Next ==
  \E p \in Proc :
    \/ Send(p)
    \/ Predict(p)
    \/ Receive(p)

NEXT == Next

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars
SPECIFICATION == Spec

(*-----------------------------------------------------------------
  Properties (placeholder)
-----------------------------------------------------------------*)
Properties == TRUE
PROPERTIES == Properties

====