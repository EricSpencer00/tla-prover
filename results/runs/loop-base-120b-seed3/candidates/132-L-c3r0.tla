---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

CONSTANTS A, B, C, bound

\* The set of possible element values
ValueSet == { A, B, C }

\* Finite sequences (functions) of length 0..bound over a set S
BoundedSeq(S) == { s : \E n \in 0..bound : s \in [1..n -> S] }

VARIABLES seq, i, cand, cnt

\* Length of a (possibly empty) sequence
Len(s) == IF s = {} THEN 0 ELSE Max(DOMAIN(s))

\* Number of occurrences of x in the current sequence
Count(x) == Cardinality({ j \in DOMAIN(seq) : seq[j] = x })

\* There exists a strict majority element in the whole sequence
MajorityExists == \E x \in ValueSet : Count(x) > Len(seq) / 2

\* Initial state
Init ==
    /\ seq \in BoundedSeq(ValueSet)
    /\ i = 1
    /\ cnt = 0
    /\ cand \in ValueSet

\* One step of the Boyer‑Moore scan
Next ==
    \/ /\ i <= Len(seq)
       /\ LET e == seq[i] IN
            /\ i' = i + 1
            /\ (cnt = 0 /\ cand' = e /\ cnt' = 1)
               \/ (cand = e /\ cnt' = cnt + 1 /\ cand' = cand)
               \/ (cand # e /\ cnt' = cnt - 1 /\ cand' = cand)
            /\ UNCHANGED seq
    \/ /\ i > Len(seq)
       /\ UNCHANGED <<seq, i, cand, cnt>>

\* The complete specification
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

\* Type correctness invariant
TypeOK ==
    /\ seq \in BoundedSeq(ValueSet)
    /\ i \in Nat
    /\ cnt \in Nat
    /\ cand \in ValueSet

\* Safety property: if a strict majority exists, it equals the final candidate
Correct ==
    /\ i > Len(seq)
    /\ MajorityExists
    => \E x \in ValueSet :
          Count(x) > Len(seq) / 2 /\ cand = x

\* A simple inductive invariant (extends TypeOK)
Inv ==
    /\ TypeOK
    /\ i <= Len(seq) + 1

====