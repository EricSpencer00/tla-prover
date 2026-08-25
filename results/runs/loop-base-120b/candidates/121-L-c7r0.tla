---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS CharacterSet

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES str, n, f, k, i, best, pc

\* ----------------------------------------------------------------------
\* Sentinel value used for undefined entries in the failure function
\* ----------------------------------------------------------------------
Sentinel == -1

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Rot(s, off) == [j \in 0..(n-1) |-> s[(off + j) % n]]

LexLeq(s1, s2) ==
  \E k \in 0..n :
    /\ \A j \in 0..(k-1) : s1[j] = s2[j]
    /\ (k = n \/ s1[k] <= s2[k])

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ n \in Nat \setminus {0}
  /\ str \in [0..(n-1) -> CharacterSet]
  /\ f \in [0..(2*n-1) -> (Nat \cup {Sentinel})]
  /\ k \in (Nat \cup {Sentinel})
  /\ i \in Nat
  /\ best \in 0..(n-1)
  /\ pc \in {"Running", "Done"}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  \E n0 \in Nat \ {0} :
    /\ n = n0
    /\ str \in [0..(n-1) -> CharacterSet]
    /\ f = [j \in 0..(2*n-1) |-> Sentinel]
    /\ k = Sentinel
    /\ i = 1
    /\ best = 0
    /\ pc = "Running"

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Running ==
  /\ pc = "Running"
  /\ i' = i + 1
  /\ best' \in 0..(n-1)
  /\ k' = Sentinel
  /\ f' = f
  /\ pc' = IF i' < 2 * n THEN "Running" ELSE "Done"
  /\ UNCHANGED str

DoneStutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<str, n, f, k, i, best, pc>>

Next == Running \/ DoneStutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<str, n, f, k, i, best, pc>>

Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Correctness property
\* ----------------------------------------------------------------------
Correctness ==
  /\ pc = "Done"
  /\ \A o \in 0..(n-1) : LexLeq(Rot(str, best), Rot(str, o))

\* ----------------------------------------------------------------------
\* The identifiers required by the .cfg file
\* ----------------------------------------------------------------------
\* The constant CharacterSet is declared above.
\* The specification formula is Spec.
\* The invariants are TypeInvariant and Correctness.

=============================================================================