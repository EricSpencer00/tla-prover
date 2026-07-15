---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS A, B, C, bound, Seq

\* The set of distinct element values
ElemSet == {A, B, C}

\* State variables
VARIABLES seq, i, cand, cnt

\* The next-element function for bounded sequences (Seq is a set of functions from 1..n to ElemSet)
SeqSet == { s \in [1..bound -> ElemSet] : TRUE }

\* Initialization
Init ==
    /\ seq \in SeqSet
    /\ i = 1
    /\ cand \in ElemSet
    /\ cnt = 0

\* Action for scanning the next element
Next ==
    \/ /\ i <= Len(seq)
       /\ LET x == seq[i] IN
          /\ IF cnt = 0 THEN
                /\ cand' = x
                /\ cnt' = 1
             ELSE IF cand = x THEN
                /\ cand' = cand
                /\ cnt' = cnt + 1
             ELSE
                /\ cand' = cand
                /\ cnt' = cnt - 1
          /\ i' = i + 1
          /\ UNCHANGED seq
    \/ /\ i > Len(seq)          \* No‑op when the scan is finished
       /\ UNCHANGED <<seq, i, cand, cnt>>

\* Specification
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

\* Type correctness invariant
TypeOK ==
    /\ seq \in SeqSet
    /\ i \in Nat
    /\ cand \in ElemSet
    /\ cnt \in Nat

\* Correctness invariant (no majority element can be different from the final candidate)
Correct ==
    \A e \in ElemSet :
        (Card({ j \in 1..Len(seq) : seq[j] = e }) > Len(seq) / 2) => (e = cand /\ i > Len(seq))

\* Additional inductive invariant (optional but required by the cfg)
Inv ==
    /\ TypeOK
    /\ (i > Len(seq) => (cnt = 0 \/ cnt = 1 \/ cnt = 2))

\* Liveness property: the scan eventually completes
Termination == <> (i > Len(seq))

\* The identifiers required by the .cfg
Specification == Spec
INVARIANTS == TypeOK, Correct, Inv
PROPERTIES == Termination

====