---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

(* ----------------------------------------------------------------------
   Finite character set (replaces Nat from Naturals for model checking)
   ---------------------------------------------------------------------- *)
CharacterSet == 0..9

VARIABLES input, n, i, j, k, best, pc

(* ----------------------------------------------------------------------
   Helper functions
   ---------------------------------------------------------------------- *)

CharAt(s, idx) == IF n = 0 THEN 0 ELSE s[idx % n]

Rotate(s, off) ==
  [pos \in 0..n-1 |-> CharAt(s, off + pos)]

LexLe(s1, s2) ==
  \A p \in 0..n-1 :
    ( \A q \in 0..p-1 : s1[q] = s2[q] ) => s1[p] <= s2[p]

(* ----------------------------------------------------------------------
   Initialization
   ---------------------------------------------------------------------- *)

Init ==
  /\ n \in Nat
  /\ input \in [0..n-1 -> CharacterSet]
  /\ i = 0
  /\ j = 1
  /\ k = 0
  /\ best = 0
  /\ pc = "Loop"

(* ----------------------------------------------------------------------
   Algorithm steps (Booth's algorithm, expressed with the required state)
   ---------------------------------------------------------------------- *)

LoopStep ==
  /\ pc = "Loop"
  /\ i < n /\ j < n /\ k < n
  /\ LET ci == CharAt(input, i + k)
         cj == CharAt(input, j + k)
     IN
        IF ci = cj THEN
          /\ k' = k + 1
          /\ i' = i
          /\ j' = j
          /\ pc' = "Loop"
        ELSE IF ci < cj THEN
          /\ jTmp  = j + k + 1
          /\ j'    = IF jTmp = i THEN jTmp + 1 ELSE jTmp
          /\ i'    = i
          /\ k'    = 0
          /\ pc'   = "Loop"
        ELSE
          /\ iTmp  = i + k + 1
          /\ i'    = IF iTmp = j THEN iTmp + 1 ELSE iTmp
          /\ j'    = j
          /\ k'    = 0
          /\ pc'   = "Loop"
  /\ UNCHANGED <<input, n, best>>

TerminateStep ==
  /\ pc = "Loop"
  /\ (i >= n \/ j >= n)
  /\ best' = Min(i, j)
  /\ pc'    = "Done"
  /\ UNCHANGED <<input, n, i, j, k>>

Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<input, n, i, j, k, best, pc>>

Next ==
  LoopStep \/ TerminateStep \/ Stutter

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<input, n, i, j, k, best, pc>>

(* ----------------------------------------------------------------------
   Invariants
   ---------------------------------------------------------------------- *)

TypeInvariant ==
  /\ n \in Nat
  /\ input \in [0..n-1 -> CharacterSet]
  /\ i \in Nat
  /\ j \in Nat
  /\ k \in Nat
  /\ best \in (IF n = 0 THEN {0} ELSE 0..n-1)
  /\ pc \in {"Loop", "Done"}

Correctness ==
  /\ pc = "Done"
  /\ \A off \in (IF n = 0 THEN {0} ELSE 0..n-1) :
        LexLe(Rotate(input, best), Rotate(input, off))

====