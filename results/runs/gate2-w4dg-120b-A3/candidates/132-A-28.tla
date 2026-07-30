---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

\* The three distinct model values, whose names are actual constants
\* (they are not elements of a set -- that shape is what the .cfg expects).
\* The bound parameter controls the maximum length of a sequence.
\* Sequences are built with a bounded sequence operator so the model
\* stays finite; the operator replaces Seq from the Sequences module.

\* A bounded collection of sequences over the three values, up to length bound.
BoundedSeq(V) ==
  { s \in Seq(V) : Len(s) <= bound }

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

TypeOK ==
  /\ seq \in BoundedSeq({A, B, C})
  /\ pos \in 0..bound
  /\ cand \in {A, B, C}
  /\ cnt \in 0..bound

\* The candidate is nondeterministically chosen at the start; the counter
\* starts at zero so either candidate can win only by gathering a majority.
Init ==
  /\ seq \in BoundedSeq({A, B, C})
  /\ pos = 1
  /\ cand \in {A, B, C}
  /\ cnt = 0

\* The Boyer-Moore scan: adopt a new candidate when the counter is zero,
\* increment when the current element matches the candidate, or decrement
\* otherwise.  When the scan reaches the end it stays there.
Next ==
  \/ (\E x \in {A, B, C} :
        /\ pos >= 1 /\ pos <= Len(seq)
        /\ cand' = IF cnt = 0 THEN x ELSE cand
        /\ cnt' = IF cnt = 0 \/ seq[pos] = cand THEN cnt + 1 ELSE cnt)
        /\ pos' = pos + 1
        /\ UNCHANGED seq
  \/ (pos >= 1 /\ pos >= Len(seq)) /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

\* The real correctness property: a true majority must be the surviving
\* candidate after the scan has run its course.
Correct ==
  (pos > Len(seq) /\ 2 * Cardinality({i \in 1..Len(seq) : seq[i] = cand}) > Len(seq))
    => cand = seq[1]

\* The inductive invariant: the counter never exceeds the scanned length,
\* and it is never zero mid-scan, which is what stops the scan from stalling.
Inv ==
  /\ cnt <= Len(seq)
  /\ (cnt = 0 => pos = 1)

\* A full scan always completes under weak fairness.
Complete ==
  (pos > Len(seq)) WF_vars Next

====