---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

VARIABLES seq, cand, cnt, pos
vars == <<seq, cand, cnt, pos>>

Init ==
  /\ seq = <<>>
  /\ cand = 0
  /\ cnt = 0
  /\ pos = 0

Reset ==
  /\ pos = 5
  /\ seq' = <<>>
  /\ cand' = 0
  /\ cnt' = 0
  /\ pos' = 0

Read(v) ==
  /\ pos < 5
  /\ seq' = Append(seq, v)
  /\ cand' = IF cnt = 0 THEN v ELSE cand
  /\ cnt' = IF cnt = 0 THEN 1 ELSE IF cand = v THEN cnt + 1 ELSE cnt - 1
  /\ pos' = pos + 1

Spec == Init /\ [][Reset \/ (\E v \in Value : Read(v))]_vars

TypeOK ==
  /\ seq \in Seq(Value)
  /\ cand \in Value
  /\ cnt \in 0..5
  /\ pos \in 0..5

Occurrences(x, s) == Cardinality({ i \in 1..Len(s) : s[i] = x })

Majority(x) == 2 * Occurrences(x, seq) > Len(seq)

Inv ==
  /\ \A x \in Value : Majority(x) => x = cand
  /\ \A x \in Value : Majority(x) => cnt > 0

Correct == Inv

====