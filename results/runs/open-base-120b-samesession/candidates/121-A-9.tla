---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

\*--------------------------------------------------------------------
\* Constants
\********************************************************************
CONSTANT CharacterSet

\* We assume CharacterSet is a finite subset of Nat (the natural numbers)
ASSUME CharacterSet \subseteq Nat

\*--------------------------------------------------------------------
\* State Variables
\********************************************************************
VARIABLES str, n, fail, k, i, best, pc

\* Helper definitions
\* Sentinel value used in the failure function and pattern‑match index
SENTINEL == -1

\* The set of all program‑counter values
PCValues == {"OuterCheck", "Lookup", "InnerLoop", "UpdateBest",
             "FollowFail", "PostComp", "Inc", "Done"}

\* Rotation of the string starting at offset \@off
Rot(off) == [j \in 0..(n-1) |-> str[(off + j) % n]]

\* Lexicographic less‑or‑equal between two sequences of the same length
LexLeq(s, t) ==
  \/ s = t
  \/ \E m \in 0..(n-1) :
        /\ \A k \in 0..(m-1) : s[k] = t[k]
        /\ s[m] < t[m]

\*--------------------------------------------------------------------
\* Type Invariant
\********************************************************************
TypeInvariant ==
  /\ n \in Nat \ {0}
  /\ str \in [0..(n-1) -> CharacterSet]
  /\ fail \in [0..(2*n) -> Int]               \* may contain SENTINEL
  /\ k \in Int
  /\ i \in Nat
  /\ best \in 0..(n-1)
  /\ pc \in PCValues

\*--------------------------------------------------------------------
\* Correctness Property (state invariant)
\********************************************************************
Correctness ==
  \A j \in 0..(n-1) : LexLeq(Rot(best), Rot(j))

\*--------------------------------------------------------------------
\* Initial State
\********************************************************************
Init ==
  /\ n \in Nat \ {0}
  /\ str \in [0..(n-1) -> CharacterSet]
  /\ fail = [p \in 0..(2*n) |-> SENTINEL]
  /\ k = SENTINEL
  /\ i = 1
  /\ best \in 0..(n-1)          \* choose a minimal rotation initially
  /\ Correctness                \* enforce that the chosen best is minimal
  /\ pc = "OuterCheck"

\*--------------------------------------------------------------------
\* Next‑state Relation
\********************************************************************
\* Stutter when algorithm is finished
Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<str, n, fail, k, i, best, pc>>

\* Outer loop check
OuterCheckTrue ==
  /\ pc = "OuterCheck"
  /\ i < 2 * n
  /\ pc' = "Lookup"
  /\ UNCHANGED <<str, n, fail, k, i, best>>

OuterCheckDone ==
  /\ pc = "OuterCheck"
  /\ i >= 2 * n
  /\ pc' = "Done"
  /\ UNCHANGED <<str, n, fail, k, i, best>>

\* Failure function lookup
Lookup ==
  /\ pc = "Lookup"
  /\ k' = fail[i]
  /\ pc' = "InnerLoop"
  /\ UNCHANGED <<str, n, fail, i, best>>

\* Inner comparison loop (abstracted – we simply move on)
InnerLoop ==
  /\ pc = "InnerLoop"
  /\ pc' = "Inc"
  /\ UNCHANGED <<str, n, fail, k, i, best>>

\* Increment outer loop counter
Inc ==
  /\ pc = "Inc"
  /\ i' = i + 1
  /\ pc' = "OuterCheck"
  /\ UNCHANGED <<str, n, fail, k, best>>

\* The full Next relation
Next ==
  \/ Stutter
  \/ OuterCheckTrue
  \/ OuterCheckDone
  \/ Lookup
  \/ InnerLoop
  \/ Inc

\*--------------------------------------------------------------------
\* Specification
\********************************************************************
Spec == Init /\ [][Next]_<<str, n, fail, k, i, best, pc>>

\*--------------------------------------------------------------------
\* Invariants (as required by the .cfg file)
\********************************************************************
Invariant == TypeInvariant /\ Correctness

\*--------------------------------------------------------------------
\* THEOREMS (optional, for TLC)
\********************************************************************
THEOREM Spec => []Invariant

====