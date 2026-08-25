---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANT CharacterSet

\* sentinel value used for “undefined’’ entries in the failure function
Sentinel == -1

VARIABLES str, n, fail, k, i, best, pc

vars == <<str, n, fail, k, i, best, pc>>

\* character at position p (modulo the string length)
CharAt(p) == IF n = 0 THEN 0 ELSE str[(p) % n]

\* lexicographic “≤’’ between the rotation starting at o1 and that at o2
LexLe(o1, o2) ==
  \A t \in 0..n-1 :
    IF CharAt(o1 + t) # CharAt(o2 + t) THEN
        CharAt(o1 + t) < CharAt(o2 + t)
    ELSE TRUE

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ n \in Nat \ {0}
  /\ str \in [0..n-1 -> CharacterSet]
  /\ fail \in [0..2*n -> Int]
  /\ k = Sentinel \/ k \in 0..2*n
  /\ i \in 0..2*n
  /\ best \in 0..n-1
  /\ pc \in {"OuterCheck","Lookup","InnerLoop","UpdateBest",
            "FollowFail","PostComp","Inc","Done"}

\* ----------------------------------------------------------------------
\* Correctness invariant – required only when the algorithm has terminated
\* ----------------------------------------------------------------------
Correctness ==
  (pc = "Done") => 
    \A j \in 0..n-1 :
      ( \E t \in 0..n-1 :
          CharAt(best + t) # CharAt(j + t) ) =>
        ( \A t \in 0..n-1 :
            IF CharAt(best + t) # CharAt(j + t) THEN
                CharAt(best + t) < CharAt(j + t)
            ELSE TRUE )
      /\ ( \A t \in 0..n-1 : CharAt(best + t) = CharAt(j + t) ) => best <= j

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ n \in Nat \ {0}
  /\ str \in [0..n-1 -> CharacterSet]
  /\ fail = [p \in 0..2*n |-> Sentinel]
  /\ k = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "OuterCheck"

\* ----------------------------------------------------------------------
\* Individual steps of the algorithm
\* ----------------------------------------------------------------------
OuterCheck ==
  /\ pc = "OuterCheck"
  /\ IF i < 2*n THEN
        /\ pc' = "Lookup"
        /\ UNCHANGED <<str, n, fail, k, best, i>>
     ELSE
        /\ pc' = "Done"
        /\ UNCHANGED <<str, n, fail, k, best, i>>

Lookup ==
  /\ pc = "Lookup"
  /\ k' = fail[(i - best) % (2*n + 1)]
  /\ pc' = "InnerLoop"
  /\ UNCHANGED <<str, n, fail, best, i>>

InnerLoop ==
  /\ pc = "InnerLoop"
  /\ IF CharAt(i) # CharAt(best + (i - best)) THEN
        /\ IF k # Sentinel THEN
               /\ pc' = "InnerLoop"
               /\ UNCHANGED <<str, n, fail, k, best, i>>
           ELSE
               /\ pc' = "PostComp"
               /\ UNCHANGED <<str, n, fail, k, best, i>>
     ELSE
        /\ pc' = "UpdateBest"
        /\ UNCHANGED <<str, n, fail, k, best, i>>

UpdateBest ==
  /\ pc = "UpdateBest"
  /\ IF CharAt(i) < CharAt(best + (i - best)) THEN
        /\ best' = i % n
     ELSE
        /\ UNCHANGED best
  /\ pc' = "FollowFail"
  /\ UNCHANGED <<str, n, fail, k, i>>

FollowFail ==
  /\ pc = "FollowFail"
  /\ k' = IF k = Sentinel THEN Sentinel ELSE fail[k]
  /\ pc' = "PostComp"
  /\ UNCHANGED <<str, n, fail, best, i>>

PostComp ==
  /\ pc = "PostComp"
  /\ IF CharAt(i) # CharAt(best + (i - best)) /\ k = Sentinel THEN
        /\ IF CharAt(i) < CharAt(best + (i - best)) THEN best' = i % n ELSE UNCHANGED best
     ELSE UNCHANGED best
  /\ fail' = [f \in DOMAIN fail |
                IF f = (i - best) % (2*n + 1) THEN
                     IF k = Sentinel THEN Sentinel ELSE k + 1
                ELSE fail[f]]
  /\ pc' = "Inc"
  /\ UNCHANGED <<str, n, k, i>>

Inc ==
  /\ pc = "Inc"
  /\ i' = i + 1
  /\ pc' = "OuterCheck"
  /\ UNCHANGED <<str, n, fail, k, best>>

Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck
  \/ Lookup
  \/ InnerLoop
  \/ UpdateBest
  \/ FollowFail
  \/ PostComp
  \/ Inc
  \/ Stutter

\* ----------------------------------------------------------------------
\* Overall specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

====