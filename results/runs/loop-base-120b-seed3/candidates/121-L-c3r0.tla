---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Integers

CONSTANTS CharacterSet

\* ----------------------------------------------------------------------
\* Finite character set (example: digits).  The actual set is supplied
\* by the .cfg file; this definition provides a default for completeness.
\* ----------------------------------------------------------------------
CharacterSet == 0..9

\* ----------------------------------------------------------------------
\* Sentinel value used to denote “undefined” entries in the failure
\* function and the pattern‑match index.
\* ----------------------------------------------------------------------
Sentinel == -1

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES str, Len, Failure, k, i, best, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Rotation of the string starting at offset o (as a function from
\* 0..Len-1 to characters).
Rot(o) == [t \in 0..Len-1 |-> str[(o + t) % Len]]

\* Lexicographic “less‑or‑equal’’ between two rotations.
LexLe(s1, s2) ==
  \E n \in 0..Len :
    (\A j \in 0..n-1 : s1[j] = s2[j]) /\
    (n = Len \/ s1[n] < s2[n])

\* The minimal rotation offset (ties broken by the smallest offset).
MinRot(s) ==
  LET offsets == 0..Len-1 IN
    CHOOSE o \in offsets :
      \A o2 \in offsets : LexLe(Rot(o), Rot(o2))

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ Len \in 1..MaxLen
  /\ str \in [0..Len-1 -> CharacterSet]
  /\ Failure = [j \in 0..2*Len-1 |-> Sentinel]
  /\ k = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "Check"

\* MaxLen is a constant that must be provided by the model configuration.
CONSTANT MaxLen

\* ----------------------------------------------------------------------
\* Algorithmic steps (highly abstracted)
\* ----------------------------------------------------------------------
Check ==
  /\ pc = "Check"
  /\ i < 2*Len
  /\ pc' = "Done"
  /\ best' = MinRot(str)
  /\ UNCHANGED << Len, str, Failure, k, i >>

CheckDone ==
  /\ pc = "Check"
  /\ i >= 2*Len
  /\ pc' = "Done"
  /\ best' = MinRot(str)
  /\ UNCHANGED << Len, str, Failure, k, i >>

Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED << str, Len, Failure, k, i, best, pc >>

Next ==
  \/ Check
  \/ CheckDone
  \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_<<str, Len, Failure, k, i, best, pc>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ Len \in Nat
  /\ Len > 0
  /\ str \in [0..Len-1 -> CharacterSet]
  /\ Failure \in [0..2*Len-1 -> (Sentinel \cup Nat)]
  /\ (k = Sentinel) \/ k \in Nat
  /\ i \in 1..2*Len
  /\ best \in 0..Len-1
  /\ pc \in {"Check", "Done"}

\* ----------------------------------------------------------------------
\* Correctness: upon termination, ‘best’ yields the lexicographically
\* minimal rotation.
\* ----------------------------------------------------------------------
Correctness ==
  pc = "Done" =>
    \A o \in 0..Len-1 : LexLe(Rot(best), Rot(o))

\* ----------------------------------------------------------------------
\* Exported identifiers required by the .cfg file
\* ----------------------------------------------------------------------
\* The specification formula
Spec

\* The invariants
TypeInvariant
Correctness

====