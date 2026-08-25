---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

\*--------------------------------------------------------------------
\* CONSTANTS
\*--------------------------------------------------------------------
CONSTANTS CharacterSet

\*--------------------------------------------------------------------
\* PARAMETERS
\*--------------------------------------------------------------------
Sentinel == -1

\*--------------------------------------------------------------------
\* VARIABLES
\*--------------------------------------------------------------------
VARIABLES str, len, fail, pi, i, best, pc

vars == << str, len, fail, pi, i, best, pc >>

\*--------------------------------------------------------------------
\* Helper definitions
\*--------------------------------------------------------------------
\* Length of a zero‑indexed sequence (function with domain 0..len-1)
Len(s) == Cardinality(DOMAIN s)

\* Rotation of a zero‑indexed sequence by offset ``off``
Rot(s, off) ==
  [j \in 0..(Len(s)-1) |-> s[(off + j) % Len(s)]]

\* Lexicographic less‑or‑equal for two rotations of equal length
LexLe(s1, s2) ==
  \E n \in 0..Len(s1) :
    /\ \A j \in 0..(n-1) : s1[j] = s2[j]
    /\ (n = Len(s1)) \/ s1[n] < s2[n]

\*--------------------------------------------------------------------
\* Initial state
\*--------------------------------------------------------------------
Init ==
  /\ str \in [0..(len-1) -> CharacterSet]    \* the string itself
  /\ len = Len(str)
  /\ fail = [j \in 0..(2*len-1) |-> Sentinel]
  /\ pi = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "Check"

\*--------------------------------------------------------------------
\* Actions corresponding to the labelled steps of Booth's algorithm
\*--------------------------------------------------------------------
Check ==
  /\ pc = "Check"
  /\ IF i < 2*len THEN pc' = "Lookup" ELSE pc' = "Done"
  /\ UNCHANGED <<str, len, fail, pi, best, i>>

Lookup ==
  /\ pc = "Lookup"
  /\ pi' = fail[(best + i) % (2*len)]
  /\ pc' = "Inner"
  /\ UNCHANGED <<str, len, fail, best, i>>

Inner ==
  /\ pc = "Inner"
  /\ LET a == str[(best + i) % len] IN
        b == IF pi = Sentinel THEN Sentinel ELSE str[(best + pi) % len] IN
     IF pi = Sentinel THEN
        pc' = "Post"
     ELSE IF a # b THEN
        pc' = "Post"
     ELSE
        \* characters equal – continue the inner comparison
        pc' = "Inner"
  /\ UNCHANGED <<str, len, fail, best, i>>

Post ==
  /\ pc = "Post"
  /\ LET a == str[(best + i) % len] IN
        b == IF pi = Sentinel THEN Sentinel ELSE str[(best + pi) % len] IN
        newFail == IF pi = Sentinel THEN Sentinel ELSE pi + 1 IN
        updBest == IF a # b /\ a < b THEN (i % len) ELSE best IN
        updFail == IF pi = Sentinel
                    THEN [fail EXCEPT ![(best + i) % (2*len)] = Sentinel]
                    ELSE [fail EXCEPT ![(best + i) % (2*len)] = newFail] IN
     /\ best' = updBest
     /\ fail' = updFail
     /\ pi' = pi
  /\ pc' = "Inc"
  /\ UNCHANGED <<str, len, i>>

Inc ==
  /\ pc = "Inc"
  /\ i' = i + 1
  /\ pc' = "Check"
  /\ UNCHANGED <<str, len, fail, pi, best>>

Done ==
  /\ pc = "Done"
  /\ UNCHANGED vars

\* Stuttering step to stay in the final state
Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  \/ Check
  \/ Lookup
  \/ Inner
  \/ Post
  \/ Inc
  \/ Done
  \/ Stutter

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\*--------------------------------------------------------------------
\* Type invariant
\*--------------------------------------------------------------------
TypeInvariant ==
  /\ str \in [0..(len-1) -> CharacterSet]
  /\ len = Len(str)
  /\ fail \in [0..(2*len-1) -> (Sentinel \cup 0..(2*len-1))]
  /\ pi \in (Sentinel \cup 0..(2*len-1))
  /\ i \in 0..(2*len)
  /\ best \in 0..(len-1)
  /\ pc \in {"Check","Lookup","Inner","Post","Inc","Done"}

\*--------------------------------------------------------------------
\* Correctness property (lexicographically minimal rotation)
\*--------------------------------------------------------------------
Correctness ==
  /\ pc = "Done"
  /\ \A off \in 0..(len-1) :
        LexLe( Rot(str, best), Rot(str, off) )

\*--------------------------------------------------------------------
\* End of module
\*--------------------------------------------------------------------
====