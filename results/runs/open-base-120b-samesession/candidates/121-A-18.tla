---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Integers

CONSTANTS CharacterSet

(* CharacterSet is a finite subset of Nat for model checking *)
ASSUME CharacterSet \subseteq Nat
ASSUME FiniteSet(CharacterSet)

VARIABLES str, n, ff, p, i, best, pc

Sentinel == -1

(* Rotation of the string starting at offset i *)
Rot(i) == [k \in 0..n-1 |-> str[(i + k) % n]]

(* Lexicographic less-or-equal between two zero‑indexed sequences of length n *)
LexLeq(s1, s2) ==
  \E k \in 0..n :
    (k = n) \/
    (\A l \in 0..k-1 : s1[l] = s2[l]) /\ s1[k] <= s2[k]

(* The (lexicographically) minimal rotation offset *)
BestOffset(str, n) ==
  CHOOSE i \in 0..n-1 :
    \A j \in 0..n-1 : LexLeq(Rot(i), Rot(j))

Init ==
  /\ n \in Nat
  /\ n > 0
  /\ str \in [0..n-1 -> CharacterSet]
  /\ ff = [j \in 0..2*n-1 |-> Sentinel]
  /\ p = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "OuterCheck"

Next ==
  \/ /\ pc = "OuterCheck"
     /\ i < 2*n
     /\ pc' = "Inc"
     /\ i' = i + 1
     /\ UNCHANGED <<str, n, ff, p, best>>
  \/ /\ pc = "OuterCheck"
     /\ i >= 2*n
     /\ pc' = "ComputeBest"
     /\ best' = BestOffset(str, n)
     /\ UNCHANGED <<str, n, ff, p, i>>
  \/ /\ pc = "Inc"
     /\ pc' = "OuterCheck"
     /\ i' = i + 1
     /\ UNCHANGED <<str, n, ff, p, best>>
  \/ /\ pc = "ComputeBest"
     /\ pc' = "Done"
     /\ UNCHANGED <<str, n, ff, p, i, best>>
  \/ /\ pc = "Done"
     /\ UNCHANGED <<str, n, ff, p, i, best, pc>>

Spec == Init /\ [][Next]_<<str, n, ff, p, i, best, pc>>

TypeInvariant ==
  /\ str \in [0..n-1 -> CharacterSet]
  /\ n \in Nat
  /\ ff \in [0..2*n-1 -> (Nat \cup {Sentinel})]
  /\ p \in (Nat \cup {Sentinel})
  /\ i \in Nat
  /\ best \in 0..n-1
  /\ pc \in {"OuterCheck", "Inc", "ComputeBest", "Done"}

Correctness ==
  pc = "Done" =>
    \A j \in 0..n-1 : LexLeq(Rot(best), Rot(j))

====