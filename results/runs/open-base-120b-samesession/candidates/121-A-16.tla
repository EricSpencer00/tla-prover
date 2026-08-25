---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Integers, Sequences, FiniteSets, ZSequences

CONSTANT CharacterSet

\* ----------------------------------------------------------------------
\* Constants
\* ----------------------------------------------------------------------
Sentinel == -1

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES str, n, fail, k, i, best, pc

vars == <<str, n, fail, k, i, best, pc>>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Mod(p, m) == IF m = 0 THEN p ELSE p - m * (p \div m)

CharAt(p) == str[ Mod(p, n) ]

Rot(off) == [t \in 0..n-1 |-> CharAt(off + t)]

LexLeq(s1, s2) ==
  \A t \in 0..n-1 :
    LET a == s1[t] IN LET b == s2[t] IN
      IF a # b THEN a < b ELSE TRUE

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ n \in Nat \setminus {0}
  /\ str \in [0..n-1 -> CharacterSet]
  /\ fail = [j \in 0..2*n |-> Sentinel]
  /\ k = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "OuterCheck"

\* ----------------------------------------------------------------------
\* Algorithmic steps
\* ----------------------------------------------------------------------
OuterCheck ==
  /\ pc = "OuterCheck"
  /\ IF i < 2*n
        THEN /\ pc' = "Lookup"
        ELSE /\ pc' = "Done"
  /\ UNCHANGED <<str, n, fail, k, best, i>>

Lookup ==
  /\ pc = "Lookup"
  /\ k' = fail[ Mod(i - best, 2*n+1) ]
  /\ pc' = "InnerLoop"
  /\ UNCHANGED <<str, n, fail, best, i>>

InnerLoop ==
  /\ pc = "InnerLoop"
  LET cur  == CharAt(i)
      cand == CharAt(best + k + 1)
  IN
    /\ IF cur # cand THEN
          /\ IF k # Sentinel THEN
                /\ k' = fail[ Mod(best + k + 1, 2*n+1) ]
                /\ pc' = "InnerLoop"
             ELSE
                /\ k' = Sentinel
                /\ pc' = "PostComp"
          ELSE
                /\ k' = k + 1
                /\ pc' = "InnerLoop"
    /\ UNCHANGED <<str, n, fail, best, i>>

PostComp ==
  /\ pc = "PostComp"
  LET cur  == CharAt(i)
      cand == CharAt(best + k + 1)
  IN
    /\ IF cur # cand /\ cur < cand
          THEN best' = i - k - 1
          ELSE best' = best
    /\ fail' = [fail EXCEPT ![ Mod(i - best, 2*n+1) ] =
                 IF cur # cand
                    THEN Sentinel
                    ELSE k + 1]
    /\ pc' = "Inc"
    /\ UNCHANGED <<str, n, k, i>>

Inc ==
  /\ pc = "Inc"
  /\ i' = i + 1
  /\ pc' = "OuterCheck"
  /\ UNCHANGED <<str, n, fail, k, best>>

Done ==
  /\ pc = "Done"
  /\ UNCHANGED vars

\* ----------------------------------------------------------------------
\* Next-state relation (allows a stuttering step after termination)
\* ----------------------------------------------------------------------
Next ==
  \/ OuterCheck
  \/ Lookup
  \/ InnerLoop
  \/ PostComp
  \/ Inc
  \/ Done
  \/ [][TRUE]_vars   \* additional stuttering

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ n \in Nat \setminus {0}
  /\ str \in [0..n-1 -> CharacterSet]
  /\ fail \in [0..2*n -> Int]          \* entries are either Sentinel or a Nat
  /\ k \in Int
  /\ i \in Nat
  /\ best \in 0..n-1
  /\ pc \in {"OuterCheck","Lookup","InnerLoop","PostComp","Inc","Done"}

Correctness ==
  /\ pc = "Done"
  /\ \A j \in 0..n-1 : LexLeq( Rot(best), Rot(j) )

\* ----------------------------------------------------------------------
\* Exported identifiers required by the .cfg file
\* ----------------------------------------------------------------------
\* The constant CharacterSet is declared above.
\* The main specification is Spec.
\* The invariants are TypeInvariant and Correctness.

====