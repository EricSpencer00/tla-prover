---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants
\* ----------------------------------------------------------------------
CONSTANT CharacterSet

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES str, len, fail, k, i, best, pc

\* ----------------------------------------------------------------------
\* Sentinels and helper definitions
\* ----------------------------------------------------------------------
Sentinel == -1

\* Zero‑indexed view of the string: a function from 0..len-1 to characters
Str(i) == IF i \in 0..len-1 THEN str[i] ELSE CharacterSet

\* Modulo operation that works for len = 0 (returns 0 in that case)
Mod(i, n) == IF n = 0 THEN 0 ELSE i % n

\* Rotation of the string starting at offset o
Rotation(o) == [j \in 0..len-1 |-> Str( Mod(o + j, len) )]

\* Lexicographic ≤ between two zero‑indexed sequences of equal length
LexLe(s1, s2) ==
  \E k \in 0..len :
    (\A j \in 0..k-1 : s1[j] = s2[j]) /\ (k = len \/ s1[k] <= s2[k])

\* Predicate stating that best is a lexicographically least rotation
IsLeastRotation ==
  \A o \in 0..len-1 : LexLe(Rotation(best), Rotation(o))

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ len \in Nat
  /\ str \in [0..len-1 -> CharacterSet]
  /\ fail = [j \in 0..2*len-1 |-> Sentinel]
  /\ k = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "OuterCheck"

\* ----------------------------------------------------------------------
\* Algorithmic steps (state‑machine)
\* ----------------------------------------------------------------------
OuterCheck ==
  /\ pc = "OuterCheck"
  /\ IF i < 2 * len
       THEN pc' = "Lookup"
       ELSE pc' = "Done"
  /\ UNCHANGED <<str, len, fail, k, i, best>>

Lookup ==
  /\ pc = "Lookup"
  /\ k' = fail[i]
  /\ pc' = "Compare"
  /\ UNCHANGED <<str, len, fail, i, best>>

Compare ==
  /\ pc = "Compare"
  /\ LET curPos  == Mod(i, len)
         candPos == Mod(best + (k+1), len)
         curChar == Str(curPos)
         candChar == Str(candPos)
     IN
        IF curChar = candChar THEN
           /\ k' = k + 1
           /\ pc' = "Compare"          \* continue inner comparison
        ELSE IF curChar < candChar THEN
           /\ best' = Mod(i - k - 1, len)   \* found a smaller rotation
           /\ pc' = "PostComp"
        ELSE
           /\ pc' = "PostComp"
  /\ UNCHANGED <<str, len, fail, i>>

PostComp ==
  /\ pc = "PostComp"
  /\ IF k # Sentinel
        THEN /\ k' = fail[k]               \* follow failure chain
             /\ pc' = "Compare"
        ELSE /\ fail[i] = IF k = Sentinel THEN Sentinel
                           ELSE k + 1
             /\ pc' = "Increment"
  /\ UNCHANGED <<str, len, i, best>>

Increment ==
  /\ pc = "Increment"
  /\ i' = i + 1
  /\ pc' = "OuterCheck"
  /\ UNCHANGED <<str, len, fail, k, best>>

Done ==
  /\ pc = "Done"
  /\ UNCHANGED <<str, len, fail, k, i, best, pc>>

Next ==
  \/ OuterCheck
  \/ Lookup
  \/ Compare
  \/ PostComp
  \/ Increment
  \/ Done

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<str, len, fail, k, i, best, pc>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ len \in Nat
  /\ str \in [0..len-1 -> CharacterSet]
  /\ fail \in [0..2*len-1 -> Int]
  /\ (k = Sentinel \/ k \in 0..len-1)
  /\ i \in 0..2*len
  /\ best \in 0..len-1
  /\ pc \in {"OuterCheck","Lookup","Compare","PostComp","Increment","Done"}

Correctness == (pc = "Done") => IsLeastRotation

\* ----------------------------------------------------------------------
\* End of module
\* ----------------------------------------------------------------------
====