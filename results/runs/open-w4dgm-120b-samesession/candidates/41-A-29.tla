---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* d0 is the default timeout interval. The two intervals never coincide, so
\* alive-sending and crash-prediction are separate steps in every process.
VARIABLES suspect, timeout, notHeard, clock, outbox

vars == <<suspect, timeout, notHeard, clock, outbox>>

MaxT == d0 + 2
MaxH == d0 + 2

TimedOut(p) == {q \in Proc : p # q /\ notHeard[p][q] > timeout[p][q]}
DidSend(p) == \E m \in outbox : m.origin = p
DidPredict(p) == \E m \in outbox : m.kind = "predict" /\ m.origin = p

TypeOK ==
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> [Proc -> 0..MaxT]]
  /\ notHeard \in [Proc -> [Proc -> 0..MaxH]]
  /\ clock \in [Proc -> 0..MaxH]
  /\ outbox \subseteq Messages

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ notHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = {}

SendAlive(p) ==
  /\ (clock[p] % SendPoint) = 0
  /\ (clock[p] % PredictPoint) # 0
  /\ outbox' = outbox \cup {[origin |-> p, dest |-> q, kind |-> "alive"] : q \in Proc \ {p}}
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ notHeard' = [notHeard EXCEPT ![p] = [q \in Proc |->
        IF q = p \/ (q \in TimedOut(p) /\ notHeard[p][q] < MaxH) THEN notHeard[p][q] + 1 ELSE notHeard[p][q]]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ (clock[p] % PredictPoint) = 0
  /\ (clock[p] % SendPoint) # 0
  /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \cup TimedOut(p)]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ notHeard' = [notHeard EXCEPT ![p] = [q \in Proc |->
        IF q \in TimedOut(p) THEN notHeard[p][q] + 1 ELSE notHeard[p][q]]]
  /\ UNCHANGED <<timeout, outbox>>

Receive(p, m) ==
  /\ m \in outbox
  /\ m.dest = p
  /\ outbox' = outbox \ {m}
  /\ suspect' = [suspect EXCEPT ![p] = IF m.kind = "alive" THEN suspect[p] \ {m.origin} ELSE suspect[p]]
  /\ timeout' = [timeout EXCEPT ![p][m.origin] =
        IF m.kind = "alive" /\ m.origin \in suspect[p] /\ timeout[p][m.origin] < MaxT
           THEN timeout[p][m.origin] + 1 ELSE timeout[p][m.origin]]
  /\ notHeard' = [notHeard EXCEPT ![p][m.origin] = IF m.kind = "alive" THEN 0 ELSE notHeard[p][m.origin]]
  /\ UNCHANGED clock

Tick(p) ==
  /\ (clock[p] % SendPoint) # 0
  /\ (clock[p] % PredictPoint) # 0
  /\ clock[p] < MaxH
  /\ ~DidSend(p)
  /\ ~DidPredict(p)
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ notHeard' = [notHeard EXCEPT ![p] = [q \in Proc |-> IF q \in TimedOut(p) /\ notHeard[p][q] < MaxH THEN notHeard[p][q] + 1 ELSE notHeard[p][q]]]
  /\ UNCHANGED <<suspect, timeout, outbox>>

ResetClocks == /\ \A p \in Proc : clock[p] > MaxH /\ clock' = [p \in Proc |-> 0] /\ UNCHANGED <<suspect, timeout, notHeard, outbox>>

Next ==
  \/ \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Tick(p)
  \/ \E p \in Proc, m \in Messages : Receive(p, m)
  \/ ResetClocks

Spec == Init /\ [][Next]_vars

====