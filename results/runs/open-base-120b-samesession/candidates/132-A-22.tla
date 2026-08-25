---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

\* The set of possible element values
ValueSet == { A, B, C }

\* Bounded version of the standard Seq operator
BoundedSeq(S) == { s \in Seq(S) : Len(s) <= bound }

VARIABLES seq, i, cand, cnt

\* Initial state
Init ==
    /\ seq \in BoundedSeq(ValueSet)
    /\ i = 1
    /\ cand \in ValueSet
    /\ cnt = 0

\* Scan the next element according to the Boyer‑Moore algorithm
Scan ==
    /\ i <= Len(seq)
    /\ LET x == seq[i] IN
        \/ /\ cnt = 0
           /\ cand' = x
           /\ cnt' = 1
           /\ i' = i + 1
        \/ /\ cnt > 0 /\ cand = x
           /\ cand' = cand
           /\ cnt' = cnt + 1
           /\ i' = i + 1
        \/ /\ cnt > 0 /\ cand # x
           /\ cand' = cand
           /\ cnt' = cnt - 1
           /\ i' = i + 1

\* Stutter when the scan is finished
Done ==
    /\ i > Len(seq)
    /\ UNCHANGED <<seq, i, cand, cnt>>

Next == Scan \/ Done

\* Type correctness invariant
TypeOK ==
    /\ seq \in BoundedSeq(ValueSet)
    /\ i \in Nat
    /\ cand \in ValueSet
    /\ cnt \in Nat

\* Inductive invariant of the algorithm
Inv ==
    /\ (cnt = 0) \/
       ( Cardinality({ j \in 1..(i-1) : seq[j] = cand })
         - Cardinality({ j \in 1..(i-1) : seq[j] # cand }) ) = cnt

\* Correctness: after a full scan, any true majority must equal the candidate
Correct ==
    /\ i > Len(seq)
    /\ \E m \in ValueSet :
          ( Cardinality({ j \in 1..Len(seq) : seq[j] = m }) > Len(seq) / 2 )
          => cand = m

\* The full specification
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

====