---- MODULE MCMajority ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS A, B, C, bound

ValueSet == {A, B, C}

VARIABLES seq, pos, cand, ct

vars == <<seq, pos, cand, ct>>

BoundedSeq(S) == {f \in Seq(S) : Len(f) <= bound}

TypeOK ==
  /\ seq \in BoundedSeq(ValueSet)
  /\ pos \in 1..(bound + 1)
  /\ cand \in ValueSet
  /\ ct \in 0..bound

Init ==
  /\ seq \in BoundedSeq(ValueSet)
  /\ pos = 1
  /\ cand \in ValueSet
  /\ ct = 0

\* Boyer-Moore scan: three cases depending on whether the current counter
\* is zero, matches the current element, or disagrees with it.
Next ==
  /\ pos <= Len(seq)
  /\ \/ \E x \in ValueSet :
        /\ pos <= Len(seq)
        /\ seq[pos] = x
        /\ ct = 0
        /\ cand' = x
        /\ ct' = 1
        /\ pos' = pos + 1
     \/ \E x \in ValueSet :
        /\ pos <= Len(seq)
        /\ seq[pos] = x
        /\ ct > 0
        /\ cand = x
        /\ ct' = ct + 1
        /\ pos' = pos + 1
     \/ \E x \in ValueSet :
        /\ pos <= Len(seq)
        /\ seq[pos] = x
        /\ ct > 0
        /\ cand # x
        /\ ct' = ct - 1
        /\ pos' = pos + 1)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Correctness: any element with strict majority must agree with the
\* candidate left after a complete scan.
Correct ==
  \A x \in ValueSet : ((2 * Cardinality({i \in 1..Len(seq) : seq[i] = x}) > Len(seq)) => cand = x)

\* The usual Boyer-Moore invariant: the recorded counter never exceeds the
\* number of times the candidate actually appears in the scanned prefix.
Inv ==
  \A i \in 1..(pos - 1) :
    (seq[i] = cand => ct <= Cardinality({j \in 1..i : seq[j] = cand}))

Complete == (pos > Len(seq))

SpecComplete == Spec /\ WF_vars(Complete)

====