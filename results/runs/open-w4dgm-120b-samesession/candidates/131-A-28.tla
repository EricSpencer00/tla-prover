---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets, MajorityBase

CONSTANTS Value

ASSUME Value \in (Nat \ {0}) \ {1}

VARIABLES pos, cand, seen, total, seq

vars == <<pos, cand, seen, total, seq>>

Init ==
  /\ pos = 0
  /\ cand = 0
  /\ seen = 0
  /\ total = 0
  /\ seq = {}

Next(v) ==
  /\ pos < Value
  /\ candidate' = IF cand = 0 THEN v ELSE cand
  /\ seen' = IF cand = 0 \/ cand = v THEN seen + 1 ELSE seen
  /\ pos' = pos + 1
  /\ total' = total + 1
  /\ seq' = seq \cup {<<pos, v>>}

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ pos \in 0..Value
  /\ cand \in 0..Value
  /\ seen \in 0..Value
  /\ total \in 0..Value
  /\ seq \subseteq (0..Value) \X (0..Value)

Majority(n) ==
  /\ n \in seq
  /\ count(seq, n[2]) > total \div 2
  /\ n[2] = cand

Inv ==
  \A n \in seq : Majority(n)

Correct == Inv

====