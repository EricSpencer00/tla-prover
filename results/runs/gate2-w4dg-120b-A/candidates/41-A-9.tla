---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspect, timeout, lastHeard, clock, pending

vars == << suspect, timeout, lastHeard, clock, pending >>

TypeOK ==
  /\ suspect \subseteq [from: Proc, to: Proc]
  /\ timeout \in [Proc -> Nat]
  /\ lastHeard \in [Proc -> Nat]
  /\ clock \in [Proc -> Nat]
  /\ pending \subseteq Messages

Init ==
  /\ suspect = {}
  /\ timeout = [p \in Proc |-> d0]
  /\ lastHeard = [p \in Proc |-> 0]
  /\ clock = [p \in Proc |-> 0]
  /\ pending = {}

Ready(p) == \A q \in Proc \ {p} : << p, q >> \notin pending

SendAlive(p) ==
  /\ Ready(p)
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ pending' = pending \cup {<< p, q >> : q \in Proc \ {p}}
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [q \in Proc |-> IF q = p \lor lastHeard[q] >= timeout[p] THEN lastHeard[q] ELSE lastHeard[q] + 1]
  /\ UNCHANGED << suspect, timeout >>

Predict(p) ==
  /\ Ready(p)
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = suspect \cup {<< p, q >> : q \in Proc \ {p} /\ lastHeard[q] >= timeout[p]}
  /\ lastHeard' = [q \in Proc |-> IF lastHeard[q] >= timeout[p] THEN lastHeard[q] + 1 ELSE lastHeard[q]]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ UNCHANGED << timeout, pending >>

Receive(p) ==
  /\ Ready(p)
  /\ clock[p] % SendPoint # 0
  /\ clock[p] % PredictPoint # 0
  /\ \E m \in pending :
       /\ m.to = p
       /\ pending' = pending \ {m}
       /\ lastHeard' = [lastHeard EXCEPT ![m.from] = 0]
       /\ suspect' = suspect \ {<< p, m.from >>}
       /\ timeout' = [timeout EXCEPT ![m.from] = IF << p, m.from >> \in suspect THEN timeout[m.from] + 1 ELSE timeout[m.from]]
  /\ clock' = [clock EXCEPT ![p] = IF clock[p] >= SendPoint /\ clock[p] >= PredictPoint /\ clock[p] >= timeout[p] THEN 0 ELSE clock[p] + 1]

Next ==
  \/ \E p \in Proc : SendAlive(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc : Receive(p)

Spec == Init /\ [][Next]_vars

====