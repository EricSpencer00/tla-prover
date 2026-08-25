---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

\* ----------------------------------------------------------------------
\* Sentinel value used for undefined entries in the failure function.
\* ----------------------------------------------------------------------
SENTINEL == -1

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES str, n, fail, k, i, best, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Lexicographic less-or-equal between two rotations identified by their
\* starting offsets.
LexLe(off1, off2) ==
  \E j \in 0..(n-1) :
    ( \A k \in 0..(j-1) :
        str[(off1 + k) % n] = str[(off2 + k) % n] )
    /\ ( str[(off1 + j) % n] < str[(off2 + j) % n] )
  \/ ( \A k \in 0..(n-1) :
        str[(off1 + k) % n] = str[(off2 + k) % n] )
      /\ off1 <= off2

\* Choose the offset of the lexicographically minimal rotation.
MinimalRotation ==
  CHOOSE off \in 0..(n-1) :
    \A off2 \in 0..(n-1) : LexLe(off, off2)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ n \in Nat
  /\ str \in [0..(n-1) -> CharacterSet]
  /\ fail = [p \in 0..(2*n) |-> SENTINEL]
  /\ k = SENTINEL
  /\ i = 1
  /\ best = 0
  /\ pc = "Run"

\* ----------------------------------------------------------------------
\* Next-state relation (abstracted algorithm)
\* ----------------------------------------------------------------------
Next ==
  \/ /\ pc = "Run"
     /\ i < 2 * n
     /\ i' = i + 1
     /\ UNCHANGED <<str, n, fail, k, best, pc>>
  \/ /\ pc = "Run"
     /\ i >= 2 * n
     /\ best' = MinimalRotation
     /\ pc' = "Done"
     /\ UNCHANGED <<str, n, fail, k, i>>
  \/ /\ pc = "Done"
     /\ UNCHANGED <<str, n, fail, k, i, best, pc>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<str, n, fail, k, i, best, pc>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ CharacterSet \subseteq Nat
  /\ n \in Nat
  /\ str \in [0..(n-1) -> CharacterSet]
  /\ fail \in [0..(2*n) -> (Nat \cup {SENTINEL})]
  /\ k \in (Nat \cup {SENTINEL})
  /\ i \in Nat
  /\ best \in 0..(n-1)
  /\ pc \in {"Run", "Done"}

\* ----------------------------------------------------------------------
\* Correctness invariant (holds once the algorithm terminates)
\* ----------------------------------------------------------------------
Correctness ==
  /\ pc = "Done"
  /\ \A off \in 0..(n-1) : LexLe(best, off)

=============================================================================