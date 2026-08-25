---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

\* Assume bound is a natural number
ASSUME bound \in Nat

\* Finite set of possible values
Values == {A, B, C}

\* Bounded sequence operator (replaces Seq from Sequences)
BoundedSeq(S) == { s \in Seq(S) : Len(s) <= bound }

\* State variables
VARIABLES seq, i, cand, cnt

vars == <<seq, i, cand, cnt>>

\* Initial state
Init ==
    /\ seq \in BoundedSeq(Values)
    /\ i = 1
    /\ cand \in Values
    /\ cnt = 0

\* One step of the Boyer‑Moore scan
Next ==
    \/ /\ i <= Len(seq)
       /\ LET x == seq[i] IN
          /\ CASE
                /\ cnt = 0      -> /\ cand' = x
                                   /\ cnt'  = 1
                /\ cand = x     -> /\ cand' = cand
                                   /\ cnt'  = cnt + 1
                /\ cand # x     -> /\ cand' = cand
                                   /\ cnt'  = cnt - 1
          /\ i' = i + 1
          /\ UNCHANGED seq
    \/ /\ i > Len(seq)       \* scan finished
       /\ UNCHANGED <<seq, i, cand, cnt>>

\* Specification
Spec == Init /\ [][Next]_vars

\* Type correctness invariant
TypeOK ==
    /\ seq \in BoundedSeq(Values)
    /\ i \in Nat
    /\ cand \in Values
    /\ cnt \in Nat

\* Main correctness property:
\* If a true majority exists in the whole sequence, after the scan finishes
\* the candidate equals that majority element.
Correct ==
    /\ i > Len(seq)
    /\ ( \E e \in Values :
            Cardinality({ j \in 1..Len(seq) : seq[j] = e }) > Len(seq) / 2 )
       => cand = e

\* Inductive invariant (here identical to TypeOK, can be strengthened if desired)
Inv == TypeOK

====