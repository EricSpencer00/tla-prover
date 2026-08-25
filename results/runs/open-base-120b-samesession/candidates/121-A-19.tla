---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Integers, Sequences, ZSequences

CONSTANTS CharacterSet

VARIABLES s, n, i, j, k, best, pc

\* ---------- Initialization ----------
Init ==
  /\ n \in Nat \ {0}
  /\ s \in [0 .. n-1 -> CharacterSet]
  /\ i = 0
  /\ j = 1
  /\ k = 0
  /\ best = 0
  /\ pc = "Loop"

\* ---------- Helper definitions ----------
Mod(x, m) == x - m * (x \div m)

SeqAt(off) == [t \in 0 .. n-1 |-> s[ Mod(off + t, n) ]]

LexLe(b1, b2) ==
  LET seq1 == SeqAt(b1)
      seq2 == SeqAt(b2)
  IN
    \/ \E t \in 0 .. n-1 :
         ( \A u \in 0 .. t-1 : seq1[u] = seq2[u] )
         /\ seq1[t] < seq2[t]
    \/ ( \A u \in 0 .. n-1 : seq1[u] = seq2[u] )
         /\ b1 <= b2

\* ---------- Main algorithm steps ----------
LoopStep ==
  /\ pc = "Loop"
  /\ i < n /\ j < n
  /\ LET a == s[ Mod(i + k, n) ]
         b == s[ Mod(j + k, n) ]
     IN
        IF a = b THEN
          /\ k' = k + 1
          /\ UNCHANGED <<s, n, i, j, best, pc>>
        ELSE IF a > b THEN
          /\ i' = i + k + 1
          /\ i' = IF i' = j THEN i' + 1 ELSE i'
          /\ k' = 0
          /\ UNCHANGED <<s, n, j, best, pc>>
        ELSE
          /\ j' = j + k + 1
          /\ j' = IF j' = i THEN j' + 1 ELSE j'
          /\ k' = 0
          /\ UNCHANGED <<s, n, i, best, pc>>

DoneStep ==
  /\ pc = "Loop"
  /\ (i >= n \/ j >= n)
  /\ best' = IF i < n THEN i ELSE j
  /\ pc' = "Done"
  /\ UNCHANGED <<s, n, i, j, k>>

Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<s, n, i, j, k, best, pc>>

Next ==
  LoopStep \/ DoneStep \/ Stutter

\* ---------- Specification ----------
Spec == Init /\ [] [Next]_<<s, n, i, j, k, best, pc>>

\* ---------- Invariants ----------
TypeInvariant ==
  /\ n \in Nat \ {0}
  /\ s \in [0 .. n-1 -> CharacterSet]
  /\ i \in 0 .. n
  /\ j \in 0 .. n
  /\ k \in 0 .. n
  /\ best \in 0 .. n-1
  /\ pc \in {"Loop", "Done"}

Correctness ==
  /\ pc = "Done"
  /\ \A offset \in 0 .. n-1 : LexLe(best, offset)

=============================================================================