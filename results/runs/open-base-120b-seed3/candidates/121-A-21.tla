---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets

(*--------------------------------------------------------------------
  Constants
--------------------------------------------------------------------*)
CONSTANTS CharacterSet

(*--------------------------------------------------------------------
  Sentinel value for undefined entries in the failure function
--------------------------------------------------------------------*)
Sentinel == -1

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES str, n, f, k, i, best, pc

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
Pos(i) == i % n
CandPos(best, i) == (best + i) % n

LexLeq(b, o) ==
  \A j \in 0..n-1 :
    ( \A k \in 0..j-1 : str[(b + k) % n] = str[(o + k) % n] )
    => str[(b + j) % n] <= str[(o + j) % n]

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
  /\ n \in Nat
  /\ str \in [0..n-1 -> CharacterSet]
  /\ f \in [0..2*n-1 -> Int]          \* failure function entries may be Sentinel
  /\ \A idx \in 0..2*n-1 : f[idx] = Sentinel
  /\ k = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "OuterCheck"

(*--------------------------------------------------------------------
  Actions
--------------------------------------------------------------------*)
OuterCheck ==
  /\ pc = "OuterCheck"
  /\ IF i < 2 * n
        THEN /\ pc' = "Lookup"
             /\ UNCHANGED <<str, n, f, k, i, best>>
        ELSE /\ pc' = "Done"
             /\ UNCHANGED <<str, n, f, k, i, best>>

Lookup ==
  /\ pc = "Lookup"
  /\ LET pos == (best + i) % n IN
       k' = f[pos]
  /\ pc' = "Compare"
  /\ UNCHANGED <<str, n, f, i, best>>

Compare ==
  /\ pc = "Compare"
  /\ LET curPos == Pos(i)
         candPos == CandPos(best, i)
         curChar == str[curPos]
         candChar == str[candPos] IN
       /\ IF curChar < candChar
             THEN best' = i
             ELSE best' = best
  /\ i' = i + 1
  /\ pc' = "OuterCheck"
  /\ UNCHANGED <<str, n, f, k>>

TerminateStutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<str, n, f, k, i, best, pc>>

Next ==
  \/ OuterCheck
  \/ Lookup
  \/ Compare
  \/ TerminateStutter

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec ==
  Init /\ [][Next]_<<str, n, f, k, i, best, pc>>

(*--------------------------------------------------------------------
  Type invariant
--------------------------------------------------------------------*)
TypeInvariant ==
  /\ n \in Nat
  /\ str \in [0..n-1 -> CharacterSet]
  /\ f \in [0..2*n-1 -> Int]
  /\ k \in Int
  /\ i \in Nat
  /\ best \in 0..n-1
  /\ pc \in {"OuterCheck", "Lookup", "Compare", "Done"}

(*--------------------------------------------------------------------
  Correctness property: upon termination, best points to a
  lexicographically minimal rotation.
--------------------------------------------------------------------*)
Correctness ==
  /\ pc = "Done"
  /\ \A offset \in 0..n-1 : LexLeq(best, offset)

=============================================================================