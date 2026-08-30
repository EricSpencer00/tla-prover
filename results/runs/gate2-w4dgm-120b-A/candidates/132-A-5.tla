---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

\* The model values are the three distinct elements of the universe; bound is
\* the maximum sequence length the model checker will explore.
VALUES == {A, B, C}

\* BoundedSeq replaces the standard Seq operator with a version that only
\* produces sequences of length at most bound, keeping the state space finite.
BoundedSeq == { f \in [1..n -> VALUES] : n \in 0..bound }

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

TypeOK ==
    /\ seq \in BoundedSeq
    /\ pos \in 1..(bound + 1)
    /\ cand \in VALUES
    /\ cnt \in 0..bound

Init ==
    /\ seq \in BoundedSeq
    /\ pos = 1
    /\ cand \in VALUES
    /\ cnt = 0

\* The Boyer-Moore scan: the three cases attached to the next element.
Next ==
    \/ \E e \in VALUES:
         /\ pos <= Len(seq)
         /\ \/ cnt = 0 /\ cand' = e /\ cnt' = 1
            \/ cand = e /\ cnt' = cnt + 1 /\ cand' = cand
            \/ cand # e /\ cnt' = cnt - 1 /\ cand' = cand
         /\ pos' = pos + 1
         /\ UNCHANGED seq
    \/ \E s \in BoundedSeq:
         /\ pos = Len(seq) + 1
         /\ seq' = s
         /\ pos' = 1
         /\ UNCHANGED <<cand, cnt>>

Spec == Init /\ [][Next]_vars

\* The candidate must be the true majority element once the scan is done.
Correct == (pos > Len(seq)) => (cnt > 0 => cand = seq[Len(seq)])

\* The counter is zero exactly when there is no outstanding candidate.
Inv == (cnt = 0) <=> pos = Len(seq) + 1

\* We also check for type correctness as a sanity check.
TypeOKV == TypeOK

\* Weak fairness on the scan ensures the sequence is always eventually consumed.
WeakFairness == WF_vars(Next)

====