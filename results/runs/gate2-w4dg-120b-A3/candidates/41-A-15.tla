---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

ASSUME d0 \in Nat /\ SendPoint \in Nat /\ PredictPoint \in Nat
ASSUME SendPoint > 0 /\ PredictPoint > 0
ASSUME SendPoint % PredictPoint # 0 /\ PredictPoint % SendPoint # 0

VARIABLES suspicion, tolerant, lastH, clock, outbox
vars == <<suspicion, tolerant, lastH, clock, outbox>>

RECURSIVE SumOver(_, _)
SumOver(f, S) == IF S = {} THEN 0
                 ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOver(f, S \ {x})

TypeOK ==
  /\ suspicion \in [Proc -> SUBSET Proc]
  /\ tolerant \in [Proc -> [Proc -> Nat]]
  /\ lastH \in [Proc -> [Proc -> Nat]]
  /\ clock \in [Proc -> Nat]
  /\ outbox \in [Proc -> SUBSET Messages]

Init ==
  /\ suspicion = [p \in Proc |-> {}]
  /\ tolerant = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastH = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

\* Send alive messages at multiples of SendPoint, but not at multiples of
\* PredictPoint (mutually exclusive intervals).
Send ==
  \E p \in Proc :
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ LET nm == {m \in Messages : m.to \in Proc \ {p}} IN
         /\ outbox' = [outbox EXCEPT ![p] = nm]
         /\ lastH' = [lastH EXCEPT ![p] = [q \in Proc |-> IF lastH[p][q] < tolerant[p][q]
                                                   THEN lastH[p][q] + 1 ELSE lastH[p][q]]]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ UNCHANGED <<suspicion, tolerant>>

\* Predict who has crashed at multiples of PredictPoint only.
Predict ==
  \E p \in Proc :
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspicion' = [suspicion EXCEPT ![p] =
                       {q \in Proc : lastH[p][q] > tolerant[p][q]}]
    /\ lastH' = [lastH EXCEPT ![p] = [q \in Proc |-> IF lastH[p][q] < tolerant[p][q]
                                             THEN lastH[p][q] + 1 ELSE lastH[p][q]]]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ UNCHANGED <<tolerant, outbox>>

\* Receive any messages addressed to this process, reset counters, and
\* adapt the timeout for any sender that was previously suspected.
Receive ==
  \E p \in Proc :
    /\ outbox' = [outbox EXCEPT ![p] = {}]
    /\ \E R \in SUBSET Messages :
         /\ \A m \in R : m.to = p
         /\ lastH' = [lastH EXCEPT ![p] = [q \in Proc |-> IF \E m \in R : m.from = q
                                                        THEN 0 ELSE lastH[p][q]]]
         /\ suspicion' = [suspicion EXCEPT ![p] = {q \in Proc :
                                                    ~ (\E m \in R : m.from = q)}]
         /\ tolerant' = [tolerant EXCEPT ![p] = [q \in Proc |-> IF \E m \in R : m.from = q
                                                                THEN tolerant[p][q] + 1
                                                                ELSE tolerant[p][q]]]
    /\ UNCHANGED clock

\* When the local clock has exceeded all relevant thresholds, reset it.
ResetClock ==
  \E p \in Proc :
    /\ clock[p] # 0
    /\ clock[p] > SendPoint
    /\ clock[p] > PredictPoint
    /\ \A q \in Proc : clock[p] > tolerant[p][q]
    /\ clock' = [clock EXCEPT ![p] = 0]
    /\ UNCHANGED <<suspicion, tolerant, lastH, outbox>>

Next == Send \/ Predict \/ Receive \/ ResetClock

Spec == Init /\ [][Next]_vars

====