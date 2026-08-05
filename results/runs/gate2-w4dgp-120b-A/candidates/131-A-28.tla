---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

VARIABLES seq, idx, cand, count

vars == <<seq, idx, cand, count>>

TypeOK ==
  /\ seq \in [1..3 -> Value]
  /\ idx \in 0..3
  /\ cand \in Value
  /\ count \in -3..3

Init ==
  /\ idx = 0
  /\ count = 0
  /\ \E e \in Value : cand = e
  /\ \E s \in [1..3 -> Value] : seq = s

Vote(v) ==
  /\ idx < 3
  /\ idx' = idx + 1
  /\ seq' = [seq EXCEPT ![idx + 1] = v]
  /\ IF count = 0 THEN cand' = v ELSE cand' = cand
  /\ IF count = 0 THEN count' = 1 ELSE IF cand = v THEN count' = count + 1 ELSE count' = count - 1

Idle ==
  /\ idx = 3
  /\ UNCHANGED <<seq, idx, cand, count>>

Next == (\E v \in Value : Vote(v)) \/ Idle

Spec == Init /\ [][Next]_vars

PositionsBefore(i) == {j \in 1..3 : j < i}
PositionsAfter(i) == {j \in 1..3 : j >= i}

posCount(b, S) == Cardinality({j \in S : seq[j] = b})

Inv ==
  /\ posCount(cand, {1..3}) >= 2
  /\ (idx = 3 => \A b \in Value : posCount(b, {1..3}) >= 2 => b = cand)

TypeOKInv == TypeOK
CorrectnessInv == Inv

====