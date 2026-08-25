---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets

\*--------------------------------------------------------------------
\* CONSTANTS
\*--------------------------------------------------------------------
CONSTANTS CharacterSet

\*--------------------------------------------------------------------
\* TYPE DEFINITIONS
\*--------------------------------------------------------------------
\* Sentinel value for undefined failure function entries
SENTINEL == -1

\* Values that a failure function entry may take
FailVal == Nat \/ {SENTINEL}

\*--------------------------------------------------------------------
\* STATE VARIABLES
\*--------------------------------------------------------------------
VARIABLES str, len, fail, p, i, best, pc

vars == <<str, len, fail, p, i, best, pc>>

\*--------------------------------------------------------------------
\* HELPER DEFINITIONS
\*--------------------------------------------------------------------
\* Length of a zero‑indexed string (function from 0..len-1)
Len(str) == 
  IF DOMAIN str = {} THEN 0
  ELSE Max(DOMAIN str) + 1

\* Rotation of a string by a given offset
Rot(s, off, n) == [k \in 0..n-1 |-> s[(off + k) % n]]

\* Lexicographic less‑than (strict)
LexLess(s1, s2, n) ==
  \E j \in 0..n-1 :
    ( \A k \in 0..j-1 : s1[k] = s2[k] ) /\ s1[j] < s2[j]

\* Lexicographic less‑or‑equal
LexLeq(s1, s2, n) == s1 = s2 \/ LexLess(s1, s2, n)

\*--------------------------------------------------------------------
\* INITIAL STATE
\*--------------------------------------------------------------------
Init ==
  /\ len \in Nat \ {0}
  /\ str \in [0..len-1 -> CharacterSet]
  /\ fail = [j \in 0..2*len |-> SENTINEL]
  /\ p = SENTINEL
  /\ i = 1
  /\ best = 0
  /\ pc = "Check"

\*--------------------------------------------------------------------
\* NEXT STATE RELATION
\*--------------------------------------------------------------------
Next ==
  \/ /\ pc = "Check"
     /\ IF i < 2*len
        THEN /\ pc' = "Step"
             /\ UNCHANGED <<str, len, fail, p, i, best>>
        ELSE /\ pc' = "Done"
             /\ UNCHANGED <<str, len, fail, p, i, best>>
  \/ /\ pc = "Step"
     /\ LET cand == i % len IN
        /\ IF LexLess(Rot(str, cand, len), Rot(str, best, len), len)
           THEN best' = cand
           ELSE best' = best
        /\ i' = i + 1
        /\ pc' = "Check"
        /\ UNCHANGED <<str, len, fail, p>>
  \/ /\ pc = "Done"
     /\ UNCHANGED vars

\*--------------------------------------------------------------------
\* SPECIFICATION
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\*--------------------------------------------------------------------
\* INVARIANTS
\*--------------------------------------------------------------------
TypeInvariant ==
  /\ len \in Nat \ {0}
  /\ str \in [0..len-1 -> CharacterSet]
  /\ fail \in [0..2*len -> FailVal]
  /\ p \in FailVal
  /\ i \in 1..2*len
  /\ best \in 0..len-1
  /\ pc \in {"Check", "Step", "Done"}

Correctness ==
  /\ pc = "Done"
  /\ \A offset \in 0..len-1 :
        LexLeq(Rot(str, best, len), Rot(str, offset, len), len)

\*--------------------------------------------------------------------
\* PROPERTIES (for the model checker)
\*--------------------------------------------------------------------
\* Liveness: the algorithm eventually terminates
Termination == <> (pc = "Done")

====