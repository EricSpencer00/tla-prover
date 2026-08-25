---- MODULE EPFailureDetector ----
EXTENDS Naturals, TLC

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspicion, timeout, last, clock, out

vars == << suspicion, timeout, last, clock, out >>

(*-----------------------------------------------------------------
  Initial state
-----------------------------------------------------------------*)
Init ==
  /\ suspicion = [p \in Proc |-> {}]
  /\ timeout   = [p \in Proc |-> [q \in Proc |-> IF p = q THEN 0 ELSE d0]]
  /\ last      = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock     = [p \in Proc |-> 0]
  /\ out       = [p \in Proc |-> {}]

(*-----------------------------------------------------------------
  Helper: compute the maximal relevant threshold for a process p
-----------------------------------------------------------------*)
MaxThresh(p) ==
  Max({SendPoint, PredictPoint} \cup { timeout[p][q] : q \in Proc })

(*-----------------------------------------------------------------
  Send alive messages
-----------------------------------------------------------------*)
SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ out' = [out EXCEPT ![p] = { [type |-> "alive", src |-> p, dst |-> q] : q \in Proc \ {p} }]
  /\ clock' = [clock EXCEPT ![p] =
        IF clock[p] + 1 > MaxThresh(p) THEN 0 ELSE clock[p] + 1]
  /\ last' = [last EXCEPT ![p][q] = IF q # p THEN last[p][q] + 1 ELSE last[p][q]]
  /\ UNCHANGED << suspicion, timeout >>

(*-----------------------------------------------------------------
  Make predictions (update suspicion set)
-----------------------------------------------------------------*)
Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspicion' = [suspicion EXCEPT ![p] =
        suspicion[p] \cup { q \in Proc \ {p} : last[p][q] > timeout[p][q] }]
  /\ clock' = [clock EXCEPT ![p] =
        IF clock[p] + 1 > MaxThresh(p) THEN 0 ELSE clock[p] + 1]
  /\ last' = [last EXCEPT ![p][q] = IF q # p THEN last[p][q] + 1 ELSE last[p][q]]
  /\ UNCHANGED << timeout, out >>

(*-----------------------------------------------------------------
  Receive incoming alive messages
-----------------------------------------------------------------*)
Receive(p) ==
  \E R \in SUBSET (Proc \ {p}) :
    /\ (* R is the set of processes from which p receives an alive message *)
    clock' = [clock EXCEPT ![p] =
          IF clock[p] + 1 > MaxThresh(p) THEN 0 ELSE clock[p] + 1]
    /\ last' = [last EXCEPT ![p][q] =
          IF q \in R THEN 0
          ELSE IF q # p THEN last[p][q] + 1 ELSE last[p][q]]
    /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ R]
    /\ timeout' = [timeout EXCEPT ![p][q] =
          IF q \in R /\ q \in suspicion[p] THEN timeout[p][q] + 1 ELSE timeout[p][q]]
    /\ UNCHANGED out

(*-----------------------------------------------------------------
  Next-state relation
-----------------------------------------------------------------*)
Next ==
  \/ \E p \in Proc : SendAlive(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc : Receive(p)

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
SPECIFICATION ==
  Init /\ [][Next]_vars

(*-----------------------------------------------------------------
  Type invariant
-----------------------------------------------------------------*)
TypeOK ==
  /\ suspicion \in [Proc -> SUBSET Proc]
  /\ timeout   \in [Proc -> [Proc -> Nat]]
  /\ last      \in [Proc -> [Proc -> Nat]]
  /\ clock     \in [Proc -> Nat]
  /\ out       \in [Proc -> SUBSET Messages]

(*-----------------------------------------------------------------
  Aliases required by the configuration file
-----------------------------------------------------------------*)
INIT == Init
NEXT == Next
INVARIANTS == { TypeOK }
PROPERTIES == {}

====