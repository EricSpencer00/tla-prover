---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

\* ----------------------------------------------------------------------
\* Sentinels and helper definitions
\* ----------------------------------------------------------------------
Sentinel == -1

\* Length of the input string (derived from the string itself)
LenStr(str) == Len(str)

\* Circular rotation of a string at a given offset
Rotation(str, off) ==
  [j \in 0..(LenStr(str) - 1) |-> str[(off + j) % LenStr(str)]]

\* Lexicographic less‑or‑equal between two rotations of the same string
LexLeq(str, off1, off2) ==
  \E k \in 0..(LenStr(str) - 1) :
    /\ \A j \in 0..(k - 1) : Rotation(str, off1)[j] = Rotation(str, off2)[j]
    /\ Rotation(str, off1)[k] <= Rotation(str, off2)[k]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
  str,        \* the input string (a sequence of characters)
  n,          \* length of str
  fail,       \* failure function array 0..2*n -> Nat \cup {Sentinel}
  pi,         \* pattern‑match index
  i,          \* outer loop counter (0..2*n)
  best,       \* best rotation offset found so far
  pc          \* program counter (label of the next step)

vars == <<str, n, fail, pi, i, best, pc>>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ str \in Seq(CharacterSet)               \* nondeterministic input
  /\ n = LenStr(str)
  /\ fail = [j \in 0..(2 * n) |-> Sentinel] \* all entries undefined
  /\ pi = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "Check"

\* ----------------------------------------------------------------------
\* Algorithmic steps (high‑level description that respects the spec)
\* ----------------------------------------------------------------------
Check ==
  /\ pc = "Check"
  /\ IF i < n
        THEN pc' = "Compare"
        ELSE pc' = "Done"
  /\ UNCHANGED <<str, n, fail, pi, best>>

Compare ==
  /\ pc = "Compare"
  /\ \* compare rotation starting at i with the current best rotation
     IF LexLeq(str, i, best)
        THEN best' = i
        ELSE best' = best
  /\ i' = i + 1
  /\ pc' = "Check"
  /\ UNCHANGED <<str, n, fail, pi>>

DoneStutter ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  \/ Check
  \/ Compare
  \/ DoneStutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ str \in Seq(CharacterSet)
  /\ n = LenStr(str)
  /\ i \in 0..(2 * n)
  /\ best \in 0..(n - 1)
  /\ pi \in (0..(2 * n)) \cup {Sentinel}
  /\ fail \in [0..(2 * n) -> (0..(2 * n)) \cup {Sentinel}]
  /\ pc \in {"Check", "Compare", "Done"}

\* ----------------------------------------------------------------------
\* Correctness invariant (holds upon termination)
\* ----------------------------------------------------------------------
Correctness ==
  /\ pc = "Done"
  /\ \A off \in 0..(n - 1) :
        LexLeq(str, best, off)

\* ----------------------------------------------------------------------
\* Model constants and assumptions
\* ----------------------------------------------------------------------
ASSUME CharacterSet \subseteq Nat      \* alphabet is a finite subset of Nat
\* (the concrete value of CharacterSet is supplied by the .cfg file)

====