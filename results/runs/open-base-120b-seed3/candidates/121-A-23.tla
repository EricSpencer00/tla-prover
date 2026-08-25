---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS CharacterSet

\* Sentinel value for undefined entries
Sentinel == -1

\* State variables
VARIABLES str, n, f, p, i, j, k, best, pc

\* Helper functions
Max(a, b) == IF a > b THEN a ELSE b
Min(a, b) == IF a < b THEN a ELSE b

Rot(offset) == 
  [idx \in 0..(n-1) |-> str[(idx + offset) % n]]

LexLe(off1, off2) ==
  LET s1 == Rot(off1) IN
  LET s2 == Rot(off2) IN
    \E pos \in 0..(n-1) :
        ( \A q \in 0..(pos-1) : s1[q] = s2[q] )
        /\ s1[pos] < s2[pos]
    \/ ( \A q \in 0..(n-1) : s1[q] = s2[q] )

\* Initial state
Init ==
  /\ n \in Nat
  /\ str \in [0..(n-1) -> CharacterSet]
  /\ f = [idx \in 0..(2*n - 1) |-> Sentinel]
  /\ p = Sentinel
  /\ i = 0
  /\ j = 1
  /\ k = 0
  /\ best = 0
  /\ pc = "Loop"

\* One step of Booth's algorithm (lexicographically least rotation)
AlgStep ==
  /\ pc = "Loop"
  /\ IF i < n /\ j < n /\ k < n THEN
        (* continue looping *)
        LET a == str[(i + k) % n] IN
        LET b == str[(j + k) % n] IN
        IF a = b THEN
          /\ i' = i
          /\ j' = j
          /\ k' = k + 1
        ELSE IF a > b THEN
          /\ i' = Max(i + k + 1, j + 1)
          /\ j' = j
          /\ k' = 0
        ELSE
          /\ i' = i
          /\ j' = Max(j + k + 1, i + 1)
          /\ k' = 0
        /\ pc' = "Loop"
        /\ UNCHANGED <<str, n, f, p>>
        /\ best' = IF i' < j' THEN i' ELSE j'
  ELSE
        (* termination condition reached *)
        /\ best' = Min(i, j)
        /\ pc' = "Done"
        /\ UNCHANGED <<str, n, f, p, i, j, k>>

\* Stuttering step to stay in the final state
Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<str, n, f, p, i, j, k, best, pc>>

Next == AlgStep \/ Stutter

\* State space variables tuple
Vars == <<str, n, f, p, i, j, k, best, pc>>

\* Specification
Spec == Init /\ [][Next]_Vars

\* Type invariant
TypeInvariant ==
  /\ n \in Nat
  /\ str \in [0..(n-1) -> CharacterSet]
  /\ f \in [0..(2*n - 1) -> (Nat \cup {Sentinel})]
  /\ p \in (Nat \cup {Sentinel})
  /\ i \in Nat /\ i <= n
  /\ j \in Nat /\ j <= n
  /\ k \in Nat /\ k <= n
  /\ best \in 0..(IF n = 0 THEN 0 ELSE n-1)
  /\ pc \in {"Loop", "Done"}

\* Correctness invariant
Correctness ==
  /\ pc = "Done"
  => \A s \in 0..(n-1) : LexLe(best, s)

====