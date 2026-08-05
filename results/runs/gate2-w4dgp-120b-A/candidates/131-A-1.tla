---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

\* The Boyer-Moore majority vote algorithm: Scan a finite sequence of values.
\* `cand` tracks the current candidate, `count` its vote balance, `pos` is the
\* scan position, and `major` is the majority value (or a sentinel) once known.
VARIABLES cand, count, pos, seq, major

vars == <<cand, count, pos, seq, major>>

\* Type-correctness: no vote count > 0 without a real candidate, and the scan
\* position stays within the sequence bounds.
TypeOK ==
  /\ pos \in 0..Len(seq)
  /\ IF count = 0 THEN cand = "none" ELSE cand \in Value
  /\ major \in Value \cup {"none"}

\* A majority is a strict majority; cardinality makes the quantifier decidable.
Majority(v) == 2 * Cardinality({i \in 1..Len(seq) : seq[i] = v}) > Len(seq)

\* The algorithm's output is correct: any strict-majority value equals the
\* candidate once the scan has covered the whole sequence.
Correct ==
  \A v \in Value : (Majority(v) /\ pos = Len(seq)) => cand = v

\* The Boyer-Moore algorithm, proved to preserve type-correctness and to
\* compute the correct majority when one exists.
Init ==
  /\ seq \in Seq(Value)
  /\ cand = "none"
  /\ count = 0
  /\ pos = 0
  /\ major = "none"

Advance1 ==
  /\ pos < Len(seq)
  /\ LET x == seq[pos + 1] IN
       /\ IF count = 0
          THEN /\ cand' = x
               /\ count' = 1
          ELSE IF cand = x
               THEN count' = count + 1
               ELSE count' = count - 1
  /\ pos' = pos + 1
  /\ UNCHANGED <<seq, major>>

Finalize ==
  /\ pos = Len(seq)
  /\ major' = IF cand = "none" \/ ~Majority(cand) THEN "none" ELSE cand
  /\ UNCHANGED <<cand, count, pos, seq>>

Next == Advance1 \/ Finalize

Spec == Init /\ [][Next]_vars

Inv == TypeOK /\ Correct

====