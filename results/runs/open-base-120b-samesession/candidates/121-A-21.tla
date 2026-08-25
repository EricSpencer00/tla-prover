---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

(*--------------------------------------------------------------------
  Constants and helper definitions
--------------------------------------------------------------------*)
SENTINEL == -1

(*--------------------------------------------------------------------
  Variables
--------------------------------------------------------------------*)
VARIABLES inputString, n, failure, f, k, best, pc

(* A convenient tuple of all state variables *)
vars == <<inputString, n, failure, f, k, best, pc>>

(*--------------------------------------------------------------------
  Helper functions
--------------------------------------------------------------------*)
CharAt(s, i) == s[i % n]

Rotation(s, off) == [i \in 1..n |-> s[(off + (i-1)) % n]]

LexLeq(r1, r2) ==
    \/ r1 = r2
    \/ \E i \in 1..n :
          /\ \A j \in 1..(i-1) : r1[j] = r2[j]
          /\ r1[i] < r2[i]

(*--------------------------------------------------------------------
  Initialization
--------------------------------------------------------------------*)
Init ==
    \E len \in Nat :
        /\ len >= 0
        /\ n = len
        /\ inputString \in [0..len-1 -> CharacterSet]
        /\ failure = [i \in 0..2*len-1 |-> SENTINEL]
        /\ f = SENTINEL
        /\ k = 1
        /\ best = 0
        /\ pc = "Check"

(*--------------------------------------------------------------------
  Algorithmic steps (a high‑level abstraction of Booth’s algorithm)
--------------------------------------------------------------------*)
Check ==
    /\ pc = "Check"
    /\ (k < n
        /\ pc' = "Update"
        /\ UNCHANGED <<inputString, n, failure, f, best, k>>)
    \/ (k >= n
        /\ pc' = "Done"
        /\ UNCHANGED <<inputString, n, failure, f, best, k>>)

Update ==
    /\ pc = "Update"
    /\ LET curRot == Rotation(inputString, k % n) IN
          best' = IF LexLeq(curRot, Rotation(inputString, best))
                  THEN k % n
                  ELSE best
    /\ k' = k + 1
    /\ pc' = "Check"
    /\ UNCHANGED <<inputString, n, failure, f>>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED <<inputString, n, failure, f, best, k, pc>>

Next ==
    \/ Check
    \/ Update
    \/ Done

(*--------------------------------------------------------------------
  Invariants
--------------------------------------------------------------------*)
TypeInvariant ==
    /\ n \in Nat
    /\ inputString \in [0..n-1 -> CharacterSet]
    /\ failure \in [0..2*n-1 -> Int]
    /\ f \in Int
    /\ k \in Nat
    /\ best \in 0..n-1
    /\ pc \in {"Check", "Update", "Done"}

Correctness ==
    (pc = "Done") =>
        /\ \A off \in 0..n-1 :
              LexLeq(Rotation(inputString, best), Rotation(inputString, off))
        /\ \A off \in 0..n-1 :
              (Rotation(inputString, off) = Rotation(inputString, best) => best <= off)

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

====