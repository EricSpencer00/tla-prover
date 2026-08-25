---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

VARIABLES str, n, f, k, i, best, pc

(* ------------------------------------------------------------------- *)
(* Sentinel value used to denote "undefined" entries in the failure   *)
(* function and the pattern‑match index.                               *)
(* ------------------------------------------------------------------- *)
Sentinel == -1

(* ------------------------------------------------------------------- *)
(* Helper definitions                                                  *)
(* ------------------------------------------------------------------- *)
Rot(off) == [j \in 0..n-1 |-> str[(off + j) % n]]

LexLeq(s1, s2) ==
  \E d \in 0..n :
    /\ \A j \in 0..d-1 : s1[j] = s2[j]
    /\ (d = n \/ s1[d] <= s2[d])

vars == <<str, n, f, k, i, best, pc>>

(* ------------------------------------------------------------------- *)
(* Initial state                                                       *)
(* ------------------------------------------------------------------- *)
Init ==
  /\ n \in Nat
  /\ str \in [0..n-1 -> CharacterSet]
  /\ f = [j \in 0..2*n-1 |-> Sentinel]
  /\ k = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "OuterCheck"

(* ------------------------------------------------------------------- *)
(* Actions                                                             *)
(* ------------------------------------------------------------------- *)

OuterCheck ==
  /\ pc = "OuterCheck"
  /\ IF i < 2*n THEN pc' = "Lookup" ELSE pc' = "Done"
  /\ UNCHANGED <<str, n, f, k, i, best>>

Lookup ==
  /\ pc = "Lookup"
  /\ k' = f[i % (2*n)]
  /\ pc' = "InnerLoop"
  /\ UNCHANGED <<str, n, f, i, best>>

InnerLoop ==
  /\ pc = "InnerLoop"
  /\ cur = str[i % n]
  /\ cand = str[(best + i) % n]
  /\ IF cur # cand /\ k # Sentinel THEN
        /\ pc' = "InnerLoop"
     ELSE IF cur # cand /\ k = Sentinel THEN
        /\ pc' = "PostComp"
     ELSE
        /\ pc' = "Inc"
  /\ UNCHANGED <<str, n, f, i, best>>
  /\ k' = k

PostComp ==
  /\ pc = "PostComp"
  /\ cur = str[i % n]
  /\ cand = str[(best + i) % n]
  /\ IF cur # cand /\ k = Sentinel THEN
        /\ IF cur < cand THEN best' = i % n ELSE best' = best
        /\ f' = [j \in DOMAIN f |-> IF j = i % (2*n) THEN Sentinel ELSE f[j]]
     ELSE
        /\ best' = best
        /\ f' = f
  /\ pc' = "Inc"
  /\ UNCHANGED <<str, n, i, k>>

Inc ==
  /\ pc = "Inc"
  /\ i' = i + 1
  /\ pc' = "OuterCheck"
  /\ UNCHANGED <<str, n, f, k, best>>

Done ==
  /\ pc = "Done"
  /\ UNCHANGED <<str, n, f, k, i, best, pc>>

Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<str, n, f, k, i, best, pc>>

Next ==
  \/ OuterCheck
  \/ Lookup
  \/ InnerLoop
  \/ PostComp
  \/ Inc
  \/ Done
  \/ Stutter

(* ------------------------------------------------------------------- *)
(* Specification                                                       *)
(* ------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_vars

(* ------------------------------------------------------------------- *)
(* Invariants                                                          *)
(* ------------------------------------------------------------------- *)
TypeInvariant ==
  /\ n \in Nat
  /\ str \in [0..n-1 -> CharacterSet]
  /\ f \in [0..2*n-1 -> (Sentinel \cup 0..2*n-1)]
  /\ k \in (Sentinel \cup 0..2*n-1)
  /\ i \in 0..2*n
  /\ best \in 0..n-1
  /\ pc \in {"OuterCheck","Lookup","InnerLoop","PostComp","Inc","Done"}

Correctness ==
  /\ pc = "Done"
  /\ \A off \in 0..n-1 : LexLeq(Rot(best), Rot(off))

====