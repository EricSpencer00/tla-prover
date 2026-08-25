---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES str, n, fail, pi, i, best, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Sentinel == -1

Char(pos) == 
  IF n = 0 THEN Sentinal 
  ELSE str[(pos) % n]

Rotation(off) == 
  [k \in 0..n-1 |-> str[(off + k) % n]]

LexLeq(off1, off2) ==
  \A k \in 0..n-1 :
    ( \A j \in 0..k-1 : Rotation(off1)[j] = Rotation(off2)[j] ) 
      => Rotation(off1)[k] <= Rotation(off2)[k]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ n \in Nat
  /\ str \in [0..n-1 -> CharacterSet]          \* empty domain when n = 0
  /\ fail = [j \in 0..(2*n-1) |-> Sentinel]
  /\ pi = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "OuterCheck"

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
OuterCheck ==
  /\ pc = "OuterCheck"
  /\ IF i < 2 * n 
        THEN pc' = "Lookup"
        ELSE pc' = "Done"
  /\ UNCHANGED <<str, n, fail, pi, i, best>>

Lookup ==
  /\ pc = "Lookup"
  /\ pi' = fail[(i - 1) % (2 * n)]           \* failure function lookup
  /\ pc' = "Compare"
  /\ UNCHANGED <<str, n, fail, i, best>>

Compare ==
  /\ pc = "Compare"
  /\ LET curPos  == i % n
        candPos == (best + pi) % n
        curChar == str[curPos]
        candChar == str[candPos]
     IN 
        IF curChar = candChar THEN
            /\ pi' = pi + 1
            /\ IF pi' = n 
                  THEN pc' = "Done" 
                  ELSE pc' = "Compare"
            /\ UNCHANGED <<str, n, fail, i, best>>
        ELSE
            /\ IF curChar < candChar 
                  THEN best' = i - pi
                  ELSE best' = best
            /\ pi' = Sentinel
            /\ fail' = [fail EXCEPT ![(i - 1) % (2 * n)] = 
                         IF curChar = candChar THEN Sentinel 
                         ELSE pi + 1]
            /\ pc' = "PostCompare"
            /\ UNCHANGED i

PostCompare ==
  /\ pc = "PostCompare"
  /\ LET curPos  == i % n
        candPos == (best + pi) % n
        curChar == str[curPos]
        candChar == str[candPos]
     IN 
        IF curChar # candChar /\ pi = Sentinel THEN
            /\ IF curChar < candChar THEN best' = i - pi ELSE best' = best
            /\ fail' = [fail EXCEPT ![(i - 1) % (2 * n)] = Sentinel]
        ELSE
            /\ fail' = [fail EXCEPT ![(i - 1) % (2 * n)] = pi + 1]
        /\ i' = i + 1
        /\ pc' = "OuterCheck"
        /\ UNCHANGED str
        /\ UNCHANGED n
        /\ UNCHANGED pi

Done ==
  /\ pc = "Done"
  /\ UNCHANGED <<str, n, fail, pi, i, best, pc>>

\* Stuttering after termination
Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<str, n, fail, pi, i, best, pc>>

Next ==
  \/ OuterCheck
  \/ Lookup
  \/ Compare
  \/ PostCompare
  \/ Done
  \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<str, n, fail, pi, i, best, pc>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ n \in Nat
  /\ str \in [0..n-1 -> CharacterSet]
  /\ fail \in [0..(2*n-1) -> Nat \cup {Sentinel}]
  /\ pi \in Nat \cup {Sentinel}
  /\ i \in Nat
  /\ (n = 0 => best = 0) 
     \/ (n > 0 => best \in 0..(n-1))
  /\ pc \in {"OuterCheck", "Lookup", "Compare", "PostCompare", "Done"}

Correctness ==
  /\ pc = "Done"
  /\ (n = 0 => best = 0)
  /\ (n > 0 => \A off \in 0..(n-1) : LexLeq(best, off))

\* ----------------------------------------------------------------------
\* Properties
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
THEOREM Spec => []Correctness

====