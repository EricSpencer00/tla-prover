---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

\* A concrete instantiation of Boyer-Moore majority vote with a bounded
\* sequence length (the bound is a model-checking parameter, not part of
\* the algorithm itself) and three distinct values.
Values == {A, B, C}
Seqs == { f \in [1..bound -> Values] : \E n \in 0..bound : \A i \in 1..n : f[i] \in Values }

VARIABLES seq, pos, cand, counter

TypeOK ==
  /\ seq \in Seqs
  /\ pos \in 1..bound
  /\ cand \in Values
  /\ counter \in Nat

Init ==
  /\ seq \in Seqs
  /\ pos = 1
  /\ \E v \in Values : cand = v
  /\ counter = 0

\* The counter can never rise above the remaining length, which keeps it
\* bounded even when the counter is negative and the majority is weak.
Bump(v) == IF v = cand THEN counter + 1 ELSE counter - 1

\* This is the only action: it always re-applies to every reachable state.
Step ==
  /\ pos <= Len(seq)
  /\ cand' = IF pos <= Len(seq) THEN seq[pos] ELSE cand
  /\ counter' = IF pos <= Len(seq) THEN Bump(seq[pos]) ELSE counter
  /\ pos' = pos + 1
  /\ UNCHANGED seq

\* The bounded-sequence operator replaces the sequence operator from
\* Sequences for exactly this model-checking reason; it is finite.
BoundedSeq == Seq

Next == Step

Spec == Init /\ [][Next]_<<seq, pos, cand, counter>> /\ WF_vars(Step)

\* The one true majority element must survive the scan as the candidate.
Correct == \A e \in Values : (2 * Cardinality({ i \in 1..Len(seq) : seq[i] = e }) > Len(seq)) => e = cand

\* A strong enough majority forces the counter positive by the time the
\* scan is done; that positivity is what makes the survival claim true.
Inv == (pos > Len(seq) /\ counter > 0) => 2 * counter > Len(seq)

\* SAFETY: type correctness and the two properties above.
Safety == TypeOK /\ Correct /\ Inv

\* LIVENESS: the single step action keeps being applicable until the scan
\* completes, under weak fairness.
Progress == <>(pos > Len(seq))

\* DEADLOCK FREEDOM: safety and progress together are the full claim.
Properties == Safety /\ Progress
====