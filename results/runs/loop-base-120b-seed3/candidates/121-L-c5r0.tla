---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Integers, Sequences

CONSTANTS CharacterSet

VARIABLES str, len, fail, k, i, best, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Sentinel == -1

Domain == 0..len-1
DoubleDomain == 0..(2*len-1)

\* Rotation of the string starting at offset \*offset\*
Rot(offset) ==
  [j \in Domain |-> str[(offset + j) % len]]

\* Lexicographic less‑or‑equal between two zero‑indexed sequences
LexLe(s, t) ==
  \A j \in Domain :
    ( \A k \in 0..j-1 : s[k] = t[k] ) => s[j] <= t[j]

\* The smallest offset producing the lexicographically minimal rotation.
MinimalOffset ==
  CHOOSE o \in Domain :
    \A p \in Domain : Rot(o) = Rot(p) => o <= p

\* ----------------------------------------------------------------------
\* State definition
\* ----------------------------------------------------------------------
vars == <<str, len, fail, k, i, best, pc>>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ len \in Nat
  /\ str \in [Domain -> CharacterSet]
  /\ fail = [j \in DoubleDomain |-> Sentinel]
  /\ k = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "Run"

\* ----------------------------------------------------------------------
\* Algorithmic steps (abstracted)
\* ----------------------------------------------------------------------
RunLoop ==
  /\ pc = "Run"
  /\ i < 2 * len
  /\ i' = i + 1
  /\ pc' = "Run"
  /\ UNCHANGED <<str, len, fail, k, best>>

DoneTransition ==
  /\ pc = "Run"
  /\ i >= 2 * len
  /\ pc' = "Done"
  /\ best' = MinimalOffset
  /\ UNCHANGED <<str, len, fail, k, i>>

Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  RunLoop \/ DoneTransition \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ len \in Nat
  /\ str \in [Domain -> CharacterSet]
  /\ fail \in [DoubleDomain -> (Sentinel \cup Nat)]
  /\ k \in (Nat \cup {Sentinel})
  /\ i \in Nat
  /\ best \in Domain
  /\ pc \in {"Run", "Done"}

Correctness ==
  /\ pc = "Done"
  /\ \A o \in Domain : LexLe(Rot(best), Rot(o))

====