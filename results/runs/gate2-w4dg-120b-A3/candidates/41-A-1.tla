---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* Each process maintains its own suspicion set, adaptive timeout intervals,
\* last-heard counters, a local clock, and a set of outgoing messages.  Send
\* and predict are guarded by the local clock so that they never fire at the
\* same instant (the two intervals are constrained to be non-multiples).

VARIABLES suspicion, timeout, lastHeard, clock, outbox

vars == << suspicion, timeout, lastHeard, clock, outbox >>

Init ==
  /\ suspicion = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> IF p = q THEN 0 ELSE d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.to = q /\ q # p}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q # p /\ lastHeard[p][q] < timeout[p][q] + 1 THEN @ + 1 ELSE @]]
  /\ UNCHANGED << suspicion, timeout >>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspicion' = [suspicion EXCEPT ![p] = @ \cup {q \in Proc : q # p /\ lastHeard[p][q] > timeout[p][q]}]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q # p /\ lastHeard[p][q] < timeout[p][q] + 1 THEN @ + 1 ELSE @]]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ UNCHANGED << timeout, outbox >>

\* Receiving is unconditional (always available); a received message resets
\* the last-heard counter and clears suspicion.  If a process that was
\* suspected turns out to be correct (its message arrives), its timeout
\* interval is increased -- the "adaptive" part of the detector.
Receive(p) ==
  /\ \E S \subseteq Messages :
       /\ \A m \in S : m.to = p
       /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                            IF \E m \in S : m.from = q THEN 0 ELSE @]]
       /\ suspicion' = [suspicion EXCEPT ![p] =
                            @ \ {q \in Proc : \E m \in S : m.from = q}]
       /\ timeout' = [timeout EXCEPT ![p] =
                            [q \in Proc |-> IF \E m \in S : m.from = q /\ q \in @ THEN @ + 1 ELSE @]]
       /\ outbox' = [outbox EXCEPT ![p] = @ \ S]
  /\ clock' = [clock EXCEPT ![p] = IF (clock[p] + 1) > SendPoint /\ (clock[p] + 1) > PredictPoint /\ (clock[p] + 1) > d0
                                    THEN 0 ELSE clock[p] + 1]

Next ==
  \/ \E p \in Proc : SendAlive(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc : Receive(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ lastHeard \in [Proc -> [Proc -> Nat]]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ suspicion \in [Proc -> SUBSET Proc]
  /\ outbox \in [Proc -> SUBSET Messages]

====