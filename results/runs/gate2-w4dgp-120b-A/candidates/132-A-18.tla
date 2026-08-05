---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

V == {A, B, C}
nats == Nat \ {0}

\* A bounded version of the standard `Seq` operator, used here to keep the
\* state space finite for model checking. Sequences are drawn from all
\* functions 1..k -> V for k ranging from zero up to the given bound.
BoundedSeq == UNION { [1..k -> V] : k \in 0..bound }

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

TypeOK ==
    /\ seq \in BoundedSeq
    /\ pos \in nats
    /\ cand \in V
    /\ cnt \in Nat

Init ==
    /\ seq \in BoundedSeq
    /\ pos = 1
    /\ cand \in V
    /\ cnt = 0

\* The Boyer-Moore scan step: three-way case on the current element.
Step ==
    /\ pos <= Len(seq)
    /\ cnt' = IF cnt = 0 THEN 1 ELSE IF seq[pos] = cand THEN cnt + 1 ELSE cnt - 1
    /\ cand' = IF cnt = 0 THEN seq[pos] ELSE cand
    /\ pos' = pos + 1
    /\ UNCHANGED seq

Next == Step

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

\* Any element that occurs in a strict majority of the sequence must be the
\* running candidate at the end of the scan.
Correct == (pos > Len(seq) /\ Len(seq) > 0) => (2 * Cardinality({i \in 1..Len(seq) : seq[i] = cand}) > Len(seq))

Inv == (pos > Len(seq) /\ Len(seq) > 0) => (cnt = 0 \/ 2 * cnt > Len(seq))

Ends == pos > Len(seq)

====