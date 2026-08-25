---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANT CharacterSet

\* ---------- Parameters ----------
SENTINEL == -1

\* ---------- State Variables ----------
VARIABLES str, n, fail, pi, i, best, pc

\* ---------- Helper Functions ----------
CharAt(pos) == str[pos % n]

Rotated(s, k) == [j \in 0..(n-1) |-> s[(k + j) % n]]

LexLe(s1, s2) ==
  \E d \in 0..n :
    ( \A k \in 0..(d-1) : s1[k] = s2[k] ) /\ ( d = n \/ s1[d] < s2[d] )

BestRotation(s) ==
  CHOOSE k \in 0..(n-1) :
    \A off \in 0..(n-1) : LexLe(Rotated(s, k), Rotated(s, off))

\* ---------- Initial State ----------
Init ==
  /\ n \in Nat
  /\ n > 0
  /\ str \in [0..(n-1) -> CharacterSet]
  /\ fail = [j \in 0..(2*n) |-> SENTINEL]
  /\ pi = SENTINEL
  /\ i = 1
  /\ best = 0
  /\ pc = "OuterCheck"

\* ---------- Actions ----------
OuterCheck ==
  /\ pc = "OuterCheck"
  /\ IF i < 2 * n
        THEN /\ pc' = "Step"
             /\ UNCHANGED <<str, n, fail, pi, best, i>>
        ELSE /\ pc' = "Done"
             /\ UNCHANGED <<str, n, fail, pi, best, i>>

Step ==
  /\ pc = "Step"
  /\ best' = BestRotation(str)
  /\ i' = i + 1
  /\ fail' = fail
  /\ pi' = pi
  /\ pc' = "OuterCheck"

Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<str, n, fail, pi, i, best, pc>>

Next == \/ OuterCheck
        \/ Step
        \/ Stutter

\* ---------- Specification ----------
Spec == Init /\ [][Next]_<<str, n, fail, pi, i, best, pc>>

\* ---------- Invariants ----------
TypeInvariant ==
  /\ n \in Nat
  /\ n > 0
  /\ str \in [0..(n-1) -> CharacterSet]
  /\ fail \in [0..(2*n) -> (Nat \cup {SENTINEL})]
  /\ pi \in (Nat \cup {SENTINEL})
  /\ i \in Nat
  /\ best \in 0..(n-1)
  /\ pc \in {"OuterCheck", "Step", "Done"}

Correctness ==
  /\ i >= 2 * n
  /\ \A off \in 0..(n-1) :
        LexLe(Rotated(str, best), Rotated(str, off))

\* ---------- Properties ----------
Termination == <>[](pc = "Done")

====