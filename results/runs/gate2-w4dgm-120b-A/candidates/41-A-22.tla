---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* Nodes send periodic alive messages, predict crashes on slow (never-failed)
\* nodes' behalf, and adapt timeouts so correct-but-slow nodes stop being
\* suspected; the safety invariant ties the shape of the model to the spec.
\* The clock is bounded and resets, so the reachable state space stays finite.

VARIABLES suspect, timeout, lastHeard, clock, outbox

vars == <<suspect, timeout, lastHeard, clock, outbox>>

Nodes == Proc \ {d0}

TypeOK ==
  /\ suspect \in [Nodes -> SUBSET Nodes]
  /\ timeout \in [Nodes -> Nat]
  /\ lastHeard \in [Nodes -> Nat]
  /\ clock \in Nat
  /\ outbox \subseteq Messages

Init ==
  /\ suspect = [n \in Nodes |-> {}]
  /\ timeout = [n \in Nodes |-> 1]
  /\ lastHeard = [n \in Nodes |-> 0]
  /\ clock = 0
  /\ outbox = {}

SendAlive ==
  /\ clock % SendPoint = 0
  /\ clock % PredictPoint # 0
  /\ outbox' = { [to |-> m, from |-> d0] : m \in Nodes }
  /\ clock' = clock + 1
  /\ lastHeard' = [n \in Nodes |-> IF n \in suspect[d0] THEN lastHeard[n] + 1 ELSE lastHeard[n]]
  /\ UNCHANGED <<suspect, timeout>>

Predict ==
  /\ clock % PredictPoint = 0
  /\ clock % SendPoint # 0
  /\ suspect' = [n \in Nodes |-> IF lastHeard[n] >= timeout[n] THEN suspect[n] \cup {n} ELSE suspect[n]]
  /\ lastHeard' = [n \in Nodes |-> IF n \in suspect[d0] THEN lastHeard[n] + 1 ELSE lastHeard[n]]
  /\ clock' = clock + 1
  /\ UNCHANGED <<timeout, outbox>>

Receive ==
  /\ clock % SendPoint # 0
  /\ clock % PredictPoint # 0
  /\ \E m \in outbox :
        /\ outbox' = outbox \ {m}
        /\ suspect' = [suspect EXCEPT ![m.to] = suspect[m.to] \ {m.from}]
        /\ timeout' = [timeout EXCEPT ![m.to] = IF m.from \in suspect[m.to] THEN @ + 1 ELSE @]
        /\ lastHeard' = [lastHeard EXCEPT ![m.to] = 0]
  /\ clock' = IF clock + 1 > SendPoint /\ clock + 1 > PredictPoint /\ clock + 1 > timeout[m.to] + 1
               THEN 0 ELSE clock + 1

Next == SendAlive \/ Predict \/ Receive

Spec ==
  /\ Init
  /\ [][Next]_vars

====