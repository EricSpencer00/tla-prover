---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS CharacterSet

\* ----------------------------------------------------------------------
\* State Variables
\* ----------------------------------------------------------------------
VARIABLES str, i, j, k, best, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Sentinel == -1

\* Length of the current string
n == Len(str)

\* Character at position p in the circular string (0‑based offset)
CharAt(p) == 
  IF n = 0 THEN Sentinel
  ELSE str[( (p % n) ) + 1]

\* Subsequence of s from index a (1‑based) to b (inclusive)
SubSeq(s, a, b) == 
  IF a > b THEN <<>>
  ELSE [t \in 1..(b - a + 1) |-> s[a + t - 1]]

\* Rotation of a string s by offset o (0‑based)
Rot(s, o) == 
  IF n = 0 THEN <<>>
  ELSE
    LET a == SubSeq(s, o + 1, n)            \* tail part
        b == SubSeq(s, 1, o)                \* head part
    IN a \o b

\* Minimum of two natural numbers
Min(a, b) == IF a <= b THEN a ELSE b

\* Lexicographic less‑or‑equal between two sequences of characters
LexLe(x, y) ==
  \A i \in 1..Min(Len(x), Len(y)) :
    ( x[i] = y[i] ) \/
    ( x[i] < y[i] /\ \A j \in 1..(i-1) : x[j] = y[j] )

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ str \in Seq(CharacterSet)            \* nondeterministic input string
  /\ i = Sentinel
  /\ j = 1
  /\ k = 0
  /\ best = 0
  /\ pc = "LoopCheck"

\* ----------------------------------------------------------------------
\* Algorithm actions (Booth's algorithm)
\* ----------------------------------------------------------------------
LoopCheck ==
  /\ pc = "LoopCheck"
  /\ IF i >= n \/ j >= n
       THEN pc' = "Done"
       ELSE pc' = "Compare"
  /\ UNCHANGED <<str, i, j, k, best>>

Compare ==
  /\ pc = "Compare"
  /\ k < n
  /\ LET a == CharAt(i + k)
         b == CharAt(j + k)
     IN
        IF a = b
        THEN /\ k' = k + 1
             /\ pc' = "Compare"
        ELSE IF a > b
        THEN /\ i' = i + k + 1
             /\ IF i' <= j THEN i' = j + 1 ELSE i' = i' \* ensure i > j
             /\ k' = 0
             /\ pc' = "LoopCheck"
        ELSE /\ j' = j + k + 1
             /\ IF j' <= i THEN j' = i + 1 ELSE j' = j' \* ensure j > i
             /\ k' = 0
             /\ pc' = "LoopCheck"
  /\ UNCHANGED str
  /\ UNCHANGED best

Done ==
  /\ pc = "Done"
  /\ best' = IF i < j THEN i ELSE j
  /\ UNCHANGED <<str, i, j, k>>
  /\ pc' = "Stutter"

Stutter ==
  /\ pc = "Stutter"
  /\ UNCHANGED <<str, i, j, k, best, pc>>

Next ==
  \/ LoopCheck
  \/ Compare
  \/ Done
  \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Vars == <<str, i, j, k, best, pc>>

Spec == Init /\ [][Next]_Vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ str \in Seq(CharacterSet)
  /\ n = Len(str)
  /\ i \in 0..n
  /\ j \in 0..n
  /\ k \in 0..n
  /\ best \in 0..(IF n = 0 THEN 0 ELSE n-1)
  /\ pc \in {"LoopCheck", "Compare", "Done", "Stutter"}

Correctness ==
  /\ n = Len(str)
  /\ \A m \in 0..(IF n = 0 THEN 0 ELSE n-1) :
        LexLe( Rot(str, best) , Rot(str, m) )

====