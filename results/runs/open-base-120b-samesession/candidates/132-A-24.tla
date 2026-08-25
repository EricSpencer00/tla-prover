---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS A, B, C, bound

\* The set of possible element values
ValueSet == { A, B, C }

\* Bounded sequences of length at most <<bound>> over <<ValueSet>>
BoundedSeq == UNION { [1..n -> ValueSet] : n \in 0..bound }

VARIABLES seq, i, cand, cnt

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in BoundedSeq
    /\ i = 1
    /\ cnt = 0
    /\ cand \in ValueSet

\* Length of the current sequence (a derived value)
LenSeq == Len(seq)

\* ----------------------------------------------------------------------
\* The main scanning step
\* ----------------------------------------------------------------------
Scan ==
    /\ i <= LenSeq
    /\ LET e == seq[i] IN
          IF cnt = 0 THEN
              /\ cand' = e
              /\ cnt' = 1
          ELSIF cand = e THEN
              /\ cand' = cand
              /\ cnt' = cnt + 1
          ELSE
              /\ cand' = cand
              /\ cnt' = cnt - 1
          END
    /\ i' = i + 1
    /\ UNCHANGED seq

\* ----------------------------------------------------------------------
\* Stuttering when the scan has finished
\* ----------------------------------------------------------------------
Done ==
    /\ i > LenSeq
    /\ UNCHANGED <<seq, i, cand, cnt>>

Next == Scan \/ Done

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>> /\ WF_vars(Scan)

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in BoundedSeq
    /\ i \in 1..(LenSeq + 1)
    /\ cand \in ValueSet
    /\ cnt \in Nat

\* ----------------------------------------------------------------------
\* Helper: count occurrences of a value in the current sequence
\* ----------------------------------------------------------------------
Count(v) ==
    IF LenSeq = 0 THEN 0
    ELSE Cardinality({ j \in 1..LenSeq : seq[j] = v })

\* ----------------------------------------------------------------------
\* Correctness property: any true majority must equal the final candidate
\* ----------------------------------------------------------------------
Correct ==
    /\ i = LenSeq + 1
    /\ \A v \in ValueSet :
          (Count(v) > LenSeq / 2) => (cand = v)

\* ----------------------------------------------------------------------
\* Inductive invariant (a typical invariant for Boyer‑Moore)
\* ----------------------------------------------------------------------
Inv ==
    /\ TypeOK
    /\ cnt >= 0
    /\ (cnt = 0) \/ (cand \in { seq[j] : j \in 1..(i - 1) })

====