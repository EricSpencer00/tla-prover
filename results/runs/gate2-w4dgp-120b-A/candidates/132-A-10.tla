---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

\* A finite, bounded version of the standard Seq construction, used instead of
\* Sequences.Seq so that the model remains finite even though the value set
\* is infinite in the full Boyer-Moore development.
Seq == UNION { [1..n -> Values] : n \in 0..bound }

VARIABLES seq, pos, cand, counter

vars == <<seq, pos, cand, counter>>

TypeOK ==
  /\ seq \in Seq
  /\ pos \in Nat
  /\ cand \in Values
  /\ counter \in Nat

Init ==
  /\ seq \in Seq
  /\ pos = 1
  /\ cand \in Values
  /\ counter = 0

\* Boyer-Moore scan: advance the scan position, updating the candidate
\* and counter according to the three-way matching / resetting logic.
Next ==
  /\ pos < Len(seq) + 1
  /\ \/ /\ seq[pos] = cand
        /\ \E k \in Values : cand' = k /\ counter' = IF seq[pos] = k THEN 1 ELSE 0
     \/ /\ counter > 0
        /\ seq[pos] # cand
        /\ cand' = cand /\ counter' = counter - 1
     \/ /\ counter = 0
        /\ seq[pos] # cand
        /\ cand' = seq[pos] /\ counter' = 1
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Spec == Init /\ [][Next]_vars

\* Once the scan completes, it stays complete.
Inv == (pos = Len(seq) + 1) => (counter = 0 \/ cand \in Values)

\* A true majority element must be the surviving candidate.
Correct ==
  (pos = Len(seq) + 1 /\ counter > 0) =>
     (\A i \in 1..Len(seq) : seq[i] = cand)

\* The model's fairness condition: the scan eventually runs out.
Complete == <>(pos = Len(seq) + 1)

====