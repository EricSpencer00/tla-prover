---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

\*--------------------------------------------------------------------
\* Constants
\*--------------------------------------------------------------------
CONSTANT MaxChar

\*--------------------------------------------------------------------
\* Finite version of Nat for substitution (right‑hand side of [ZSequences]CharacterSet)
\*--------------------------------------------------------------------
[ZSequences]CharacterSet == 0..MaxChar
CharacterSet == [ZSequences]CharacterSet

\*--------------------------------------------------------------------
\* State variables
\*--------------------------------------------------------------------
VARIABLES str,               \* input string as a function 0..n-1 -> CharacterSet
          n,                 \* length of the string (positive)
          fail,              \* failure function array 0..2*n -> Nat ∪ {sentinel}
          k,                 \* pattern‑match index (sentinel or Nat)
          i,                 \* outer loop counter (1..2*n)
          best,              \* best rotation offset (0..n-1)
          pc                 \* program counter (label of the step)

\*--------------------------------------------------------------------
\* Sentinels and helper sets
\*--------------------------------------------------------------------
sentinel == -1

\*--------------------------------------------------------------------
\* Type invariant
\*--------------------------------------------------------------------
TypeInvariant ==
    /\ n \in Nat \setminus {0}
    /\ str \in [0..n-1 -> CharacterSet]
    /\ fail \in [0..2*n -> (Nat \cup {sentinel})]
    /\ k \in (Nat \cup {sentinel})
    /\ i \in 1..2*n
    /\ best \in 0..n-1
    /\ pc \in {"OuterCheck","Done"}

\*--------------------------------------------------------------------
\* Rotation of the string by offset o
\*--------------------------------------------------------------------
Rotation(o) == [j \in 0..n-1 |-> str[(o + j) % n]]

\*--------------------------------------------------------------------
\* Lexicographic less‑or‑equal on two rotations
\*--------------------------------------------------------------------
LexLeq(s1, s2) ==
    \A j \in 0..n-1 :
        (\A k \in 0..j-1 : s1[k] = s2[k]) => s1[j] <= s2[j]

\*--------------------------------------------------------------------
\* Correctness property (minimal rotation)
\*--------------------------------------------------------------------
Correctness ==
    \A o \in 0..n-1 : LexLeq(Rotation(best), Rotation(o))

\*--------------------------------------------------------------------
\* Helper: the minimal rotation offset for a given string
\*--------------------------------------------------------------------
MinOffset ==
    CHOOSE o \in 0..n-1 :
        \A o2 \in 0..n-1 : LexLeq(Rotation(o), Rotation(o2))

\*--------------------------------------------------------------------
\* Initial state
\*--------------------------------------------------------------------
Init ==
    /\ n \in Nat \setminus {0}
    /\ str \in [0..n-1 -> CharacterSet]
    /\ fail = [j \in 0..2*n |-> sentinel]
    /\ k = sentinel
    /\ i = 1
    /\ best = 0
    /\ pc = "OuterCheck"

\*--------------------------------------------------------------------
\* Transition relation (simplified algorithmic steps)
\*--------------------------------------------------------------------
Next ==
    \/ /\ pc = "OuterCheck"
       /\ IF i < 2*n
          THEN /\ i' = i + 1
               /\ pc' = "OuterCheck"
               /\ UNCHANGED <<str, n, fail, k, best>>
          ELSE /\ best' = MinOffset
               /\ pc' = "Done"
               /\ UNCHANGED <<str, n, fail, k, i>>
    \/ /\ pc = "Done"
       /\ UNCHANGED <<str, n, fail, k, i, best, pc>>

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_<<str, n, fail, k, i, best, pc>>

\*--------------------------------------------------------------------
\* Theorems (optional, can be used by TLC)
\*--------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
THEOREM Spec => []Correctness
====