---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

\* ----------------------------------------------------------------------
\* Constants
\* ----------------------------------------------------------------------
CONSTANTS CharacterSet

\* ----------------------------------------------------------------------
\* Sentinel value for undefined failure function entries
\* ----------------------------------------------------------------------
Sentinel == -1

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES str, n, fail, i, k, best, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Rotate(s, off) ==
  [j \in 0..(n-1) |-> s[(off + j) % n]]

\* Lexicographic less-or-equal for two zero‑indexed strings of equal length
LexLe(s1, s2) ==
  \A j \in 0..(n-1) :
    ( \A p \in 0..(j-1) : s1[p] = s2[p] ) => s1[j] <= s2[j]

\* The (one of the) minimal rotation offsets of a string
MinRotation(s) ==
  CHOOSE off \in 0..(n-1) :
    \A off2 \in 0..(n-1) : LexLe(Rotate(s, off), Rotate(s, off2))

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ n \in Nat
  /\ n > 0
  /\ str \in [0..(n-1) -> CharacterSet]
  /\ fail = [j \in 0..(2*n-1) |-> Sentinel]
  /\ i = Sentinel
  /\ k = 1
  /\ best = 0
  /\ pc = "OuterCheck"

\* ----------------------------------------------------------------------
\* Actions modeling the algorithm (abstracted)
\* ----------------------------------------------------------------------
OuterCheck ==
  /\ pc = "OuterCheck"
  /\ IF k < 2*n
        THEN pc' = "IncK" /\ UNCHANGED <<str, n, fail, i, best, k>>
        ELSE pc' = "Done" /\ UNCHANGED <<str, n, fail, i, best, k>>

IncK ==
  /\ pc = "IncK"
  /\ k' = k + 1
  /\ pc' = "OuterCheck"
  /\ UNCHANGED <<str, n, fail, i, best>>

Finalize ==
  /\ pc = "Done"
  /\ best' = MinRotation(str)
  /\ UNCHANGED <<str, n, fail, i, k, pc>>

Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<str, n, fail, i, k, best, pc>>

Next ==
  \/ OuterCheck
  \/ IncK
  \/ Finalize
  \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<str, n, fail, i, k, best, pc>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ str \in [0..(n-1) -> CharacterSet]
  /\ n = Len([j \in 0..(n-1) |-> str[j]])   \* n equals the length of str
  /\ fail \in [0..(2*n-1) -> (Sentinel \cup Nat)]
  /\ i \in (Sentinel) \cup Nat
  /\ 1 <= k <= 2*n
  /\ best \in 0..(n-1)
  /\ pc \in {"OuterCheck", "IncK", "Done"}

\* ----------------------------------------------------------------------
\* Correctness invariant (holds in the terminal state)
\* ----------------------------------------------------------------------
Correctness ==
  /\ pc = "Done"
  /\ best = MinRotation(str)

====