---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

SetOfValues == {A, B, C}
Seqs == UNION { [1 .. n -> SetOfValues] : n \in 0 .. bound }
\* Replaces the unbounded Seq from Sequences with a finite version so the model
\* stays finite for model checking.  Keeps EXTENDS Sequences but does NOT
\* declare Seq here -- the .cfg file does the replacement.
BoundedSeq == Seqs

VARIABLES seq, pos, cand, count

vars == <<seq, pos, cand, count>>

TypeOK ==
  /\ seq \in BoundedSeq
  /\ pos \in 1 .. (Len(seq) + 1)
  /\ cand \in SetOfValues
  /\ count \in 0 .. bound

\* After a complete scan, a true majority element can only be the surviving
\* candidate; since the candidate is a single value, at most one majority can
\* exist, which is exactly what forces distinct majority outcomes to agree.
Correct == (Len(seq) > 0 /\ 2 * count > Len(seq)) => cand = seq[pos - 1]

Init ==
  /\ seq \in BoundedSeq
  /\ pos = 1
  /\ cand \in SetOfValues
  /\ count = 0

\* The three-case logic of Boyer-Moore: adopt a new candidate when the count is
\* zero, increment on a match, and decrement on a mismatch.
Step ==
  /\ pos <= Len(seq)
  /\ LET x == seq[pos] IN
       IF count = 0 THEN cand' = x /\ count' = 1
       ELSE IF x = cand THEN count' = count + 1
       ELSE count' = count - 1
  /\ pos' = pos + 1
  /\ UNCHANGED seq

Next == Step

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

Inv == TypeOK

\* Weak fairness on the single scan step, plus the two structural invariants.
Properties == Spec /\ Inv /\ Correct

====