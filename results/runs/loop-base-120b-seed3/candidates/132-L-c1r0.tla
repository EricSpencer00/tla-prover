---- MODULE MCMajority ----
EXTENDS Sequences, Naturals, FiniteSets

CONSTANTS A, B, C, bound

\* The set of possible element values
Values == { A, B, C }

\* BoundedSeq replaces Seq from the Sequences module.
\* It denotes all finite sequences (functions) from 1..n to V
\* where n is between 0 and the given bound.
BoundedSeq(V) == { s : \E n \in 0..bound : s \in [1..n -> V] }

VARIABLES seq, pos, cand, count

\* Length of a (possibly empty) sequence
Len(s) == IF s = {} THEN 0 ELSE Max(Domain(s))

\* Initial state: a nondeterministic sequence of bounded length,
\* scan position starts at 1, counter 0, candidate arbitrary.
Init ==
    /\ seq \in BoundedSeq(Values)
    /\ pos = 1
    /\ count = 0
    /\ cand \in Values

\* The scanning step of the Boyer‑Moore majority vote algorithm.
Next ==
    \/ /\ pos <= Len(seq)               \* still elements to scan
       /\ x = seq[pos]
       /\ \* case count = 0: adopt new candidate
          ( /\ count = 0
              /\ cand' = x
              /\ count' = 1 )
          \/ ( /\ count # 0
               /\ cand = x
               /\ cand' = cand
               /\ count' = count + 1 )
          \/ ( /\ count # 0
               /\ cand # x
               /\ cand' = cand
               /\ count' = count - 1 )
       /\ pos' = pos + 1
       /\ UNCHANGED seq
    \/ /\ pos > Len(seq)                \* scan finished, stutter
       /\ UNCHANGED <<seq, pos, cand, count>>

\* Specification
Spec == Init /\ [][Next]_<<seq, pos, cand, count>>

\* Type correctness invariant
TypeOK ==
    /\ seq \in BoundedSeq(Values)
    /\ pos \in Nat
    /\ cand \in Values
    /\ count \in Nat

\* Inductive invariant (can be strengthened as needed)
Inv == TypeOK

\* Correctness property: after the scan finishes, any true majority element
\* must equal the final candidate.
Correct ==
    (pos > Len(seq)) =>
        \A m \in Values :
            ( Cardinality({ i \in 1..Len(seq) : seq[i] = m }) > Len(seq) / 2 )
            => m = cand

====