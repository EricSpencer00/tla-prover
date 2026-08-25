---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANT CharacterSet

\* ----------------------------------------------------------------------
\* Utility definitions
\* ----------------------------------------------------------------------
Mod(i, n) == IF n = 0 THEN 0 ELSE i % n

Rot(str, n, offset) ==
  [j \in 0 .. n-1 |-> str[Mod(offset + j, n)]]

LexLe(s, t) ==
  \A j \in 0 .. Len(s)-1 :
    ( \A k \in 0 .. j-1 : s[k] = t[k] ) => s[j] <= t[j]

Len(seq) == 
  IF DOMAIN seq = {} THEN 0
  ELSE (Max(DOMAIN seq) + 1)

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES str, n, i, j, k, best, pc

\* ----------------------------------------------------------------------
\* Sentinel (not used in this formulation)
\* ----------------------------------------------------------------------
\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ n \in Nat
  /\ n > 0
  /\ str \in [0 .. n-1 -> CharacterSet]
  /\ i = 0
  /\ j = 1
  /\ k = 0
  /\ best = 0
  /\ pc = "Loop"

\* ----------------------------------------------------------------------
\* Main loop actions (Booth's algorithm)
\* ----------------------------------------------------------------------
LoopCond == i < n /\ j < n

a == str[Mod(i + k, n)]
b == str[Mod(j + k, n)]

\* Case 1: characters equal, extend match
CaseEqual ==
  /\ pc = "Loop"
  /\ LoopCond
  /\ a = b
  /\ k' = k + 1
  /\ i' = i
  /\ j' = j
  /\ best' = best
  /\ pc' = "Loop"

\* Case 2: a > b, discard i
CaseAGreater ==
  /\ pc = "Loop"
  /\ LoopCond
  /\ a # b
  /\ a > b
  /\ iTemp = i + k + 1
  /\ i' = IF iTemp = j THEN iTemp + 1 ELSE iTemp
  /\ j' = j
  /\ k' = 0
  /\ best' = best
  /\ pc' = "Loop"

\* Case 3: a < b, discard j
CaseBLess ==
  /\ pc = "Loop"
  /\ LoopCond
  /\ a # b
  /\ a < b
  /\ jTemp = j + k + 1
  /\ j' = IF jTemp = i THEN jTemp + 1 ELSE jTemp
  /\ i' = i
  /\ k' = 0
  /\ best' = best
  /\ pc' = "Loop"

\* Exit the loop when condition fails
DoneAction ==
  /\ pc = "Loop"
  /\ ~LoopCond
  /\ pc' = "Done"
  /\ best' = IF i < j THEN i ELSE j
  /\ UNCHANGED <<str, n, i, j, k>>

\* Stuttering after termination
Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<str, n, i, j, k, best, pc>>

Next ==
  \/ CaseEqual
  \/ CaseAGreater
  \/ CaseBLess
  \/ DoneAction
  \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<str, n, i, j, k, best, pc>>
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ n \in Nat
  /\ n > 0
  /\ str \in [0 .. n-1 -> CharacterSet]
  /\ i \in Nat
  /\ j \in Nat
  /\ k \in Nat
  /\ best \in 0 .. n-1
  /\ pc \in {"Loop", "Done"}

\* ----------------------------------------------------------------------
\* Correctness invariant
\* ----------------------------------------------------------------------
Correctness ==
  /\ pc = "Done"
  /\ \A shift \in 0 .. n-1 :
        LexLe(Rot(str, n, best), Rot(str, n, shift))

\* ----------------------------------------------------------------------
\* Assumptions about the character set
\* ----------------------------------------------------------------------
ASSUME CharacterSet \subseteq Nat

====