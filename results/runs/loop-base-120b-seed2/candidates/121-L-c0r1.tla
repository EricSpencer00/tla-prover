---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Finite character set (replaces Nat from Naturals for model checking)
\* ----------------------------------------------------------------------
CharacterSet == 0..3  \* example finite alphabet; adjust via the .cfg if needed

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES str, len, best, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Idx(i) == i % len

Rotate(s, k) == [j \in 0..len-1 |-> s[Idx(j + k)]]

LexLe(a, b) ==
  \E n \in 0..len-1 :
    (\A j \in 0..n-1 : a[j] = b[j]) /\ a[n] <= b[n]

Correctness ==
  \A k \in 0..len-1 : LexLe(Rotate(str, best), Rotate(str, k))

TypeInvariant ==
  /\ len \in Nat
  /\ len > 0
  /\ str \in [0..len-1 -> CharacterSet]
  /\ best \in 0..len-1
  /\ pc \in {"Run", "Done"}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ len \in Nat
  /\ len > 0
  /\ str \in [0..len-1 -> CharacterSet]
  /\ best = 0
  /\ pc = "Run"

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ /\ pc = "Run"
     /\ \E k \in 0..len-1 :
          LexLe(Rotate(str, k), Rotate(str, best))
     /\ best' = k
     /\ pc' = "Run"
     /\ UNCHANGED <<str, len>>
  \/ /\ pc = "Run"
     /\ Correctness
     /\ best' = best
     /\ pc' = "Done"
     /\ UNCHANGED <<str, len>>
  \/ /\ pc = "Done"
     /\ UNCHANGED <<str, len, best, pc>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<str, len, best, pc>>

\* ----------------------------------------------------------------------
\* Invariants (exposed for the .cfg)
\* ----------------------------------------------------------------------
TypeInvariant
Correctness
====