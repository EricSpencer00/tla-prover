---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences

(*--------------------------------------------------------------------
  The Boyer-Moore majority vote algorithm specification.
  This module introduces the constants, variables, initial predicate,
  next-state relation, and invariants required by the reference .cfg.
--------------------------------------------------------------------*)

CONSTANT Value

\* A finite non‑empty sequence of elements from the domain `Value`.
Sequence == Seq(Value)

VARIABLES seq, i, cand, cnt

\* -----------------------------------------------------------------
\* Type correctness predicate (used as an invariant)
\* -----------------------------------------------------------------
TypeOK ==
    /\ seq \in Sequence
    /\ i \in Nat
    /\ i <= Len(seq)                \* scanning index, never exceeds length
    /\ cand \in Value
    /\ cnt \in Nat

\* -----------------------------------------------------------------
\* Helper definitions
\* -----------------------------------------------------------------
\* Positions before index `i` (1‑based indexing of the sequence)
Positions(i) == { j \in Nat : 1 <= j /\ j < i }

\* Cardinality of a set (provided by FiniteSets)
Cardinality(S) == IF S = {} THEN 0 ELSE Card(S)

\* -----------------------------------------------------------------
\* Initialization
\* -----------------------------------------------------------------
Init ==
    /\ seq \in Sequence
    /\ i = 1
    /\ cand = seq[1]               \* arbitrary choice of first element
    /\ cnt = 1

\* -----------------------------------------------------------------
\* Transition relation (single step of the Boyer‑Moore algorithm)
\* -----------------------------------------------------------------
Next ==
    \/ /\ i <= Len(seq)            \* there is still an element to process
       /\ i' = i + 1
       /\ IF cnt = 0
          THEN /\ cand' = seq[i]
               /\ cnt'  = 1
          ELSE IF seq[i] = cand
               THEN /\ cand' = cand
                    /\ cnt'  = cnt + 1
               ELSE /\ cand' = cand
                    /\ cnt'  = cnt - 1
       /\ UNCHANGED << seq >>
    \/ /\ i > Len(seq)             \* after the sequence is exhausted,
       /\ UNCHANGED << i, cand, cnt, seq >>   \* stutter forever

\* -----------------------------------------------------------------
\* Specification (used by the .cfg file)
\* -----------------------------------------------------------------
Spec == Init /\ [][Next]_<< i, cand, cnt, seq >>

\* -----------------------------------------------------------------
\* Main correctness invariant (the one proved in the companion
\* BoyerMoore majority vote specification).  It states that any
\* element that occurs more than half the time in the entire sequence
\* must equal the final candidate.
\* -----------------------------------------------------------------
Correct ==
    \A v \in Value :
        (Cardinality({ j \in Nat : 1 <= j /\ j <= Len(seq) /\ seq[j] = v })
         > Len(seq) / 2)
        => v = cand

\* -----------------------------------------------------------------
\* The inductive invariant imported from the main algorithm spec.
\* It is defined here as an abbreviation of the conjunction of
\* `TypeOK` and `Correct`, making the .cfg identifier `Inv` meaningful.
\* -----------------------------------------------------------------
Inv == /\ TypeOK
       /\ Correct

=============================================================================