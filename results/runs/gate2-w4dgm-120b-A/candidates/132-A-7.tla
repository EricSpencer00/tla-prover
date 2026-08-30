---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

\* Concrete model values for the Boyer-Moore majority vote algorithm; the
\* bound parameter keeps the sequence length finite for model checking.
Values == {A, B, C}

VARIABLES seq, pos, cand, count

vars == <<seq, pos, cand, count>>

TypeOK ==
    /\ seq \in [1..bound -> Values]
    /\ pos \in 1..(bound + 1)
    /\ cand \in Values
    /\ count \in 0..bound

Init ==
    /\ \E n \in 0..bound : seq \in [1..n -> Values]
    /\ pos = 1
    /\ cand \in Values
    /\ count = 0

\* Boyer-Moore scan step: adopt a new candidate when the counter is empty,
\* increment on a match, or decrement otherwise.
Step ==
    /\ pos <= Len(seq)
    /\ LET x == seq[pos] IN
         IF count = 0 THEN /\ cand' = x
                            /\ count' = 1
         ELSE IF x = cand THEN /\ count' = count + 1
                              /\ UNCHANGED cand
         ELSE /\ count' = count - 1
              /\ UNCHANGED cand
    /\ pos' = pos + 1
    /\ UNCHANGED seq

Next == Step

\* A true majority element must survive the full Boyer-Moore scan as the
\* candidate, so any majority is equal to the final candidate.
Correct ==
    \A x \in Values :
        (2 * Cardinality({i \in 1..Len(seq) : seq[i] = x}) > Len(seq)) => x = cand

\* The candidate is always one of the three values, and the counter is
\* bounded by the sequence length.
Inv ==
    /\ cand \in Values
    /\ count <= Len(seq)

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

EventualCompletion == <>(pos > Len(seq))

\* A bounded-sequence version of Seq that only yields sequences up to the
\* configured length, keeping the model finite for checking. Extends
\* Naturals and Sequences, does NOT redeclare Seq itself.
BoundedSeq(n) == IF n = 0 THEN <<>> ELSE CHOOSE s \in Seq(n) : TRUE
====