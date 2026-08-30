---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* An eventually perfect failure detector: alive messages arrive (possibly
\* reordered or delayed), and each process times out on others adaptively.
\* Actions are gated on the local clock, so sending and predicting never
\* interleave on the same tick -- that is the design choice, not a property.

VARIABLES suspect, timeout, ticks, clock, outbox

TypeOK ==
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ ticks \in [Proc -> [Proc -> Nat]]
  /\ clock \in [Proc -> Nat]
  /\ outbox \in [Proc -> SUBSET Messages]

Reached(p, q) == <<p, q>> \in outbox

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ ticks = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {[p, q] : q \in Proc \ {p}}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ ticks' = [q \in Proc |-> [ticks[q] EXCEPT ![p] = IF ticks[q][p] < timeout[q][p] THEN ticks[q][p] + 1 ELSE ticks[q][p]]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = {q \in Proc : ticks[p][q] >= timeout[p][q]}]
  /\ ticks' = [q \in Proc |-> [ticks[q] EXCEPT ![p] = IF ticks[q][p] < timeout[q][p] THEN ticks[q][p] + 1 ELSE ticks[q][p]]]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ UNCHANGED <<timeout, outbox>>

Receive(p, q) ==
  /\ clock[p] % SendPoint # 0
  /\ clock[p] % PredictPoint # 0
  /\ q # p
  /\ Reached(q, p)
  /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {q}]
  /\ outbox' = [outbox EXCEPT ![q] = outbox[q] \ {<<q, p>>}]
  /\ ticks' = [ticks EXCEPT ![p][q] = 0]
  /\ timeout' = [timeout EXCEPT ![p][q] = IF q \in suspect[p] THEN timeout[p][q] + 1 ELSE timeout[p][q]]
  /\ clock' = [clock EXCEPT ![p] = IF clock[p] >= SendPoint \/ clock[p] >= PredictPoint THEN 0 ELSE clock[p] + 1]

Next ==
  \/ \E p \in Proc : SendAlive(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc, q \in Proc : Receive(p, q)

Spec == Init /\ [][Next]_<<suspect, timeout, ticks, clock, outbox>>

====