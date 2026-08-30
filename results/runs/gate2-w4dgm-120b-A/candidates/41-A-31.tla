---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* A correct process in an eventually perfect failure detector: it periodically
\* sends alive messages to everyone, periodically evaluates its suspicion
\* list from last-heard counters and adaptive timeouts, and never fails itself.

VARIABLES clock, outbox, timeout, lastHeard, suspect

vars == <<clock, outbox, timeout, lastHeard, suspect>>

\* Model a directed message from one correct process to another.
Message == [src: Proc, dst: Proc]

TypeOK ==
  /\ clock \in 0 .. PredictPoint
  /\ outbox \subseteq Messages
  /\ timeout \in [Proc -> Nat]
  /\ lastHeard \in [Proc -> Nat]
  /\ suspect \subseteq Proc

Init ==
  /\ clock = 0
  /\ outbox = {}
  /\ timeout = [q \in Proc |-> d0]
  /\ lastHeard = [q \in Proc |-> 0]
  /\ suspect = {}

\* Send alive messages every SendPoint ticks, but never on the same tick
\* as a prediction, which is what keeps the two processes separate.
SendAlive ==
  /\ clock % SendPoint = 0
  /\ clock % PredictPoint # 0
  /\ outbox' = {m \in outbox : m.dst \in Proc} \cup {[src |-> p, dst |-> q] : q \in Proc \ {p}}
  /\ lastHeard' = [q \in Proc |->
        IF q = p \/ lastHeard[q] >= timeout[q] THEN lastHeard[q] + 1 ELSE 1]
  /\ clock' = clock + 1
  /\ UNCHANGED <<timeout, suspect>>

\* A protected prediction: only processes not already timed out can be added
\* to the suspicion set, and never on a send tick.
Predict ==
  /\ clock % PredictPoint = 0
  /\ clock % SendPoint # 0
  /\ suspect' = suspect \cup {q \in Proc \ {p} : lastHeard[q] > timeout[q]}
  /\ lastHeard' = [q \in Proc |->
        IF q = p \/ lastHeard[q] >= timeout[q] THEN lastHeard[q] + 1 ELSE 1]
  /\ clock' = clock + 1
  /\ UNCHANGED <<timeout, outbox>>

\* Anything that is not a prediction or a send tick just delivers messages.
Deliver ==
  /\ clock % SendPoint # 0 \/ clock % PredictPoint # 0
  /\ \E m \in outbox :
        /\ outbox' = outbox \ {m}
        /\ lastHeard' = [lastHeard EXCEPT ![m.dst] = 0]
        /\ suspect' = suspect \ {m.dst}
        /\ timeout' = [timeout EXCEPT ![m.dst] = IF m.dst \in suspect THEN timeout[m.dst] + 1 ELSE timeout[m.dst]]
  /\ clock' = clock + 1

\* The local clock is finite; once it runs past every threshold it resets.
TickAndReset ==
  /\ clock' = IF clock >= PredictPoint /\ clock >= SendPoint /\ \A q \in Proc : clock >= timeout[q]
                THEN 0 ELSE clock + 1
  /\ UNCHANGED <<outbox, timeout, lastHeard, suspect>>

Next == SendAlive \/ Predict \/ Deliver \/ TickAndReset

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(TickAndReset)

====