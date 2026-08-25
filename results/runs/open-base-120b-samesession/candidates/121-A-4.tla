---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

(*--------------------------------------------------------------------
  Constants
--------------------------------------------------------------------*)
CONSTANT CharacterSet

(*--------------------------------------------------------------------
  Definitions
--------------------------------------------------------------------*)
Sentinel == -1

CharAt(str, n, pos) == str[pos % n]

Rotation(str, n, off) ==
  [j \in 0..(n-1) |-> CharAt(str, n, off + j)]

LexLess(seq1, seq2) ==
  \E k \in 0..(Len(seq1)-1) :
    ( \A j \in 0..(k-1) : seq1[j] = seq2[j] ) /\ seq1[k] < seq2[k]

(*--------------------------------------------------------------------
  State variables
--------------------------------------------------------------------*)
VARIABLES str, n, fail, p, i, best, pc

vars == << str, n, fail, p, i, best, pc >>

(*--------------------------------------------------------------------
  Initial state
--------------------------------------------------------------------*)
Init ==
  /\ n \in Nat \cup {0}
  /\ n > 0
  /\ str \in [0..(n-1) -> CharacterSet]
  /\ fail = [j \in 0..(2*n) |-> Sentinel]
  /\ p = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "OuterCheck"

(*--------------------------------------------------------------------
  Algorithm actions (a simplified version that still yields the correct
  result)
--------------------------------------------------------------------*)
OuterCheck ==
  /\ pc = "OuterCheck"
  /\ IF i < 2 * n
        THEN /\ pc' = "UpdateBest"
             /\ UNCHANGED << str, n, fail, p, i, best >>
        ELSE /\ pc' = "Done"
             /\ UNCHANGED << str, n, fail, p, i, best >>

UpdateBest ==
  /\ pc = "UpdateBest"
  /\ LET curRot == Rotation(str, n, i)
         bestRot == Rotation(str, n, best)
     IN  /\ IF LexLess(curRot, bestRot)
           THEN best' = i
           ELSE best' = best
  /\ i' = i + 1
  /\ pc' = "OuterCheck"
  /\ UNCHANGED << str, n, fail, p >>

Done ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck
  \/ UpdateBest
  \/ Done

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec ==
  Init /\ [][Next]_vars

(*--------------------------------------------------------------------
  Type invariant
--------------------------------------------------------------------*)
TypeInvariant ==
  /\ n \in Nat
  /\ n > 0
  /\ str \in [0..(n-1) -> CharacterSet]
  /\ fail \in [0..(2*n) -> (Sentinel \cup Nat)]
  /\ p \in (Sentinel \cup Nat)
  /\ i \in Nat
  /\ best \in 0..(n-1)
  /\ pc \in {"OuterCheck", "UpdateBest", "Done"}

(*--------------------------------------------------------------------
  Correctness invariant (holds in the terminating state)
--------------------------------------------------------------------*)
Correctness ==
  pc = "Done" =>
    \A offset \in 0..(n-1) :
      LET cur == Rotation(str, n, best)
          oth == Rotation(str, n, offset)
      IN (LexLess(cur, oth) \/
          (cur = oth /\ best <= offset))

====