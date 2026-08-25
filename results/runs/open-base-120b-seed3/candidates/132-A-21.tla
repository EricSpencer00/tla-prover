---- MODULE MCMajority ----
EXTENDS Sequences, Naturals, FiniteSets

CONSTANTS A, B, C, bound

\* Assume bound is a natural number (non‑negative integer)
ASSUME bound \in Nat

\* The set of possible element values
Values == { A, B, C }

\* A finite version of the sequence operator, bounded by `bound`
BoundedSeq(S) == UNION { [1..n -> S] : n \in 0..bound }

VARIABLES seq, i, cand, cnt

\* Type correctness invariant
TypeOK == 
    /\ seq \in BoundedSeq(Values)
    /\ i \in Nat
    /\ cand \in Values
    /\ cnt \in Nat

\* Initial state: any bounded sequence, start scanning at position 1,
\* nondeterministically choose an initial candidate, counter = 0
Init == 
    /\ seq \in BoundedSeq(Values)
    /\ i = 1
    /\ cand \in Values
    /\ cnt = 0

\* One step of the Boyer‑Moore scan when there is still an element to read
Scan ==
    /\ i <= Len(seq)
    /\ LET x == seq[i] IN
       CASE
         cnt = 0    -> /\ cand' = x
                       /\ cnt' = 1
         x = cand   -> /\ cand' = cand
                       /\ cnt' = cnt + 1
         OTHER     -> /\ cand' = cand
                       /\ cnt' = cnt - 1
    /\ i' = i + 1
    /\ UNCHANGED seq

\* Stuttering step after the scan is finished
Done ==
    /\ i > Len(seq)
    /\ UNCHANGED << seq, i, cand, cnt >>

Next == Scan \/ Done

\* Specification of the algorithm
Spec == Init /\ [][Next]_<< seq, i, cand, cnt >>

\* Correctness property: any element that appears more than half the time
\* must equal the final candidate after the scan completes
Correct ==
    \A v \in Values :
        ( Cardinality({ j \in 1..Len(seq) : seq[j] = v }) > Len(seq) / 2 )
        => ( i > Len(seq) => cand = v )

\* Inductive invariant (here taken to be the same as the type invariant)
Inv == TypeOK

====