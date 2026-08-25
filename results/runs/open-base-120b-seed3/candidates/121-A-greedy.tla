---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANT CharacterSet

VARIABLES str, n, best, i

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)

(* Length of a zero‑indexed sequence *)
Len(s) == IF s = {} THEN 0 ELSE Max(Domain(s)) + 1

(* Rotation of the string starting at offset off (zero‑indexed) *)
Rot(s, off) ==
  [j \in 0..n-1 |-> s[(off + j) % n]]

(* Lexicographic less‑or‑equal between two zero‑indexed sequences of length n *)
LexLe(s1, s2) ==
  \A k \in 0..n-1 :
    ( \A m \in 0..k-1 : s1[m] = s2[m] ) => s1[k] <= s2[k]

(* Set of offsets that yield a lexicographically minimal rotation *)
MinSet(s) ==
  { off \in 0..n-1 :
      \A j \in 0..n-1 : LexLe(Rot(s, off), Rot(s, j)) }

(* The smallest offset among the minimal rotations *)
MinOffset(s) ==
  CHOOSE x \in MinSet(s) : \A y \in MinSet(s) : x <= y

(* ----------------------------------------------------------------------
   Initialization
   ---------------------------------------------------------------------- *)

Init ==
  /\ n \in Nat
  /\ str \in [0..n-1 -> CharacterSet]
  /\ best = 0
  /\ i = 1

(* ----------------------------------------------------------------------
   Next‑state relation (abstracted algorithm)
   ---------------------------------------------------------------------- *)

Next ==
  \/ /\ i < 2 * n
     /\ i' = i + 1
     /\ UNCHANGED <<str, n, best>>
  \/ /\ i = 2 * n
     /\ best' = MinOffset(str)
     /\ UNCHANGED <<str, n, i>>
  \/ /\ i > 2 * n
     /\ UNCHANGED <<str, n, best, i>>

vars == <<str, n, best, i>>

(* ----------------------------------------------------------------------
   Specification, invariants and correctness property
   ---------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_vars

TypeInvariant ==
  /\ str \in [0..n-1 -> CharacterSet]
  /\ n \in Nat
  /\ best \in 0..n-1
  /\ i \in Nat

Correctness ==
  [] (i >= 2 * n =>
        /\ \A j \in 0..n-1 : LexLe(Rot(str, best), Rot(str, j))
        /\ \A j \in 0..n-1 :
            ( \A k \in 0..n-1 : Rot(str, best)[k] = Rot(str, j)[k] ) => best <= j)

====