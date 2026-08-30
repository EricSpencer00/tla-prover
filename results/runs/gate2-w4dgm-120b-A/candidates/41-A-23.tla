---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspect, timeout, sinceHeard, clock, pending

vars == <<suspect, timeout, sinceHeard, clock, pending>>

TypeOK ==
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> Nat]
  /\ sinceHeard \in [Proc -> Nat]
  /\ clock \in Nat
  /\ pending \in SUBSET Messages

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> d0]
  /\ sinceHeard = [p \in Proc |-> 0]
  /\ clock = 0
  /\ pending = {}

SendAlive ==
  /\ clock % SendPoint = 0
  /\ clock % PredictPoint # 0
  /\ pending' = {m \in pending : m.dest \notin Proc}
                 \cup {[src |-> p, dest |-> q] : p \in Proc, q \in Proc, p # q}
  /\ clock' = clock + 1
  /\ sinceHeard' = [q \in Proc |-> IF q \in suspect[p] THEN sinceHeard[q] + 1 ELSE sinceHeard[q]]
  /\ UNCHANGED <<suspect, timeout>>

Predict ==
  /\ clock % PredictPoint = 0
  /\ clock % SendPoint # 0
  /\ suspect' = [p \in Proc |-> suspect[p] \cup {q \in Proc : sinceHeard[q] > timeout[q]}]
  /\ sinceHeard' = [q \in Proc |-> IF q \in suspect[p] THEN sinceHeard[q] + 1 ELSE sinceHeard[q]]
  /\ clock' = clock + 1
  /\ UNCHANGED <<timeout, pending>>

Receive ==
  /\ clock' = IF clock + 1 > SendPoint /\ clock + 1 > PredictPoint /\ clock + 1 > timeout[p] THEN 0 ELSE clock + 1
  /\ suspect' = [p \in Proc |-> suspect[p] \ {q \in Proc : q = m.src /\ m \in pending}]
  /\ timeout' = [p \in Proc |-> IF m \in pending /\ m.src \in suspect[p] THEN timeout[p] + 1 ELSE timeout[p]]
  /\ sinceHeard' = [q \in Proc |-> IF \E m \in pending : m.dest = q THEN 0 ELSE sinceHeard[q]]
  /\ pending' = {m \in pending : m.dest \notin Proc}

Next ==
  \/ SendAlive
  \/ Predict
  \/ Receive

Spec == Init /\ [][Next]_vars

====