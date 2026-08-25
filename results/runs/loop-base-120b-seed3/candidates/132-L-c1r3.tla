---- MODULE MCMajority ----
EXTENDS Sequences, Naturals, FiniteSets

CONSTANTS A, B, C, bound

\* The set of possible element values
Values == { A, B, C }

\* BoundedSeq replaces Seq from the Sequences module.
\* It denotes all finite sequences (functions) from 1..n to V
\* where n is between 0 and the given bound.
BoundedSeq(V) == UNION { [1..n -> V] : n \in 0..bound }

VARIABLES seq, pos, cand, count

\* Length of a (possibly empty) sequence
L(s) == IF s = {} THEN 0 ELSE Max(Domain(s))

\* Initial state: a nondeterministic sequence of bounded length,
\* scan position starts at 1, counter 0, candidate arbitrary.
Init ==
    /\ seq \in BoundedSeq(Values)
    /\ pos = 1
    /\ count = 0
    /\ cand \in Values

\* The scanning step of the Boyer‑Moore majority vote algorithm.
Next ==
    \/ /\ pos <= L(seq)               \* still elements to scan
       /\ ( /\ count = 0
                /\ cand' = seq[pos]
                /\ count' = 1 )
          \/ ( /\ count # 0
                /\ cand = seq[pos]
                /\ cand' = cand
                /\ count' = count + 1 )
          \/ ( /\ count # 0
                /\ cand # seq[pos]
                /\ cand' = cand
                /\ count' = count - 1 )
       /\ pos' = pos + 1
       /\ UNCHANGED seq
    \/ /\ pos > L(seq)                \* scan finished, stutter
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
    (pos > L(seq)) =>
        \A m \in Values :
            ( Cardinality({ i \in 1..L(seq) : seq[i] = m }) > L(seq) / 2 )
            => m = cand
====