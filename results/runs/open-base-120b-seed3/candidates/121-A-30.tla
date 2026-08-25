---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT CharacterSet

\* Sentinel value used for undefined entries in the failure function
Sentinel == -1

VARIABLES str, n, fail, pi, i, best, pc

\* Helper: rotation of the string `str` by offset `off`
Rot(str, off) ==
  [j \in 0..n-1 |-> str[(off + j) % n]]

\* Lexicographic less-or-equal between two zero‑indexed sequences of equal length
LexLe(rot1, rot2) ==
  \A k \in 0..n-1 :
    ( \A j \in 0..k-1 : rot1[j] = rot2[j] ) => rot1[k] <= rot2[k]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ \E n0 \in Nat :
        /\ n0 > 0
        /\ n = n0
        /\ \E s \in [0..n0-1 -> CharacterSet] :
              str = s
        /\ fail = [j \in 0..(2*n0)-1 |-> Sentinel]
        /\ pi = Sentinel
        /\ i = 1
        /\ best = 0
        /\ pc = "Running"

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ /\ pc = "Running"
        /\ i < 2 * n
        /\ LET off == i % n
               cand == Rot(str, off)
               cur  == Rot(str, best)
           IN
              /\ IF LexLe(cand, cur) THEN best' = off ELSE best' = best
        /\ i' = i + 1
        /\ pc' = "Running"
        /\ UNCHANGED <<str, n, fail, pi>>
  \/ /\ pc = "Running"
        /\ i >= 2 * n
        /\ pc' = "Done"
        /\ UNCHANGED <<str, n, fail, pi, i, best>>
  \/ /\ pc = "Done"
        /\ UNCHANGED <<str, n, fail, pi, i, best, pc>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ n \in Nat
  /\ n > 0
  /\ str \in [0..n-1 -> CharacterSet]
  /\ fail \in [0..(2*n)-1 -> (Nat \cup {Sentinel})]
  /\ pi \in (Nat \cup {Sentinel})
  /\ i \in Nat
  /\ best \in 0..n-1
  /\ pc \in {"Running", "Done"}

\* ----------------------------------------------------------------------
\* Correctness: upon termination `best` points to the lexicographically
\* smallest rotation of `str`
\* ----------------------------------------------------------------------
Correctness ==
  /\ pc = "Done"
  /\ \A off \in 0..n-1 :
        LET rotOff  == Rot(str, off)
            rotBest == Rot(str, best)
        IN LexLe(rotBest, rotOff)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<str, n, fail, pi, i, best, pc>>

Spec == Init /\ [][Next]_vars

=============================================================================