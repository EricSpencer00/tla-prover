---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Integers, Sequences

CONSTANTS CharacterSet

(*--------------------------------------------------------------------
  Sentinel value used for “undefined’’ entries in the failure function.
--------------------------------------------------------------------*)
Sentinel == -1

VARIABLES str, n, fail, pi, i, best, pc

vars == << str, n, fail, pi, i, best, pc >>

(*--------------------------------------------------------------------
  Initial state: a nondeterministic string over CharacterSet and the
  algorithm’s auxiliary variables.
--------------------------------------------------------------------*)
Init ==
  /\ n \in Nat
  /\ str \in [0..n-1 -> CharacterSet]
  /\ fail = [j \in 0..2*n-1 |-> Sentinel]
  /\ pi = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "Running"

(*--------------------------------------------------------------------
  Helper definitions
--------------------------------------------------------------------*)
Rot(str, offset) ==
  [j \in 0..n-1 |-> str[(offset + j) % n]]

LexLe(s1, s2) ==
  \E m \in 0..n :
    /\ \A j \in 0..m-1 : s1[j] = s2[j]
    /\ (m = n \/ s1[m] <= s2[m])

MinRot(str) ==
  CHOOSE off \in 0..n-1 :
    \A k \in 0..n-1 : LexLe(Rot(str, off), Rot(str, k))

(*--------------------------------------------------------------------
  Algorithmic steps (high‑level model)
--------------------------------------------------------------------*)
StepInc ==
  /\ pc = "Running"
  /\ i < 2*n
  /\ i' = i + 1
  /\ UNCHANGED << str, n, fail, pi, best >>
  /\ pc' = "Running"

StepDone ==
  /\ pc = "Running"
  /\ i >= 2*n
  /\ best' = MinRot(str)
  /\ pc' = "Done"
  /\ UNCHANGED << str, n, fail, pi, i >>

Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  StepInc \/ StepDone \/ Stutter

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [] [Next]_vars

(*--------------------------------------------------------------------
  Invariants required by the .cfg file
--------------------------------------------------------------------*)
TypeInvariant ==
  /\ n \in Nat
  /\ str \in [0..n-1 -> CharacterSet]
  /\ fail \in [0..2*n-1 -> (Nat \cup {Sentinel})]
  /\ pi \in (Nat \cup {Sentinel})
  /\ i \in Nat
  /\ best \in 0..n-1
  /\ pc \in {"Running", "Done"}

Correctness ==
  /\ pc = "Done"
  /\ best = MinRot(str)
  /\ \A k \in 0..n-1 : LexLe(Rot(str, best), Rot(str, k))

====