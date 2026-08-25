---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, TLC

CONSTANTS CharacterSet

\* ----------------------------------------------------------------------
\* Finite sentinel value used to indicate undefined entries in the failure
\* function array.
\* ----------------------------------------------------------------------
Sentinel == -1

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES str, n, f, k, i, best, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Idx(j) == j % n                     \* modulo indexing for circularity

Rot(s, off) == [j \in 0..(n-1) |-> s[(off + j) % n]]

LexLe(s1, s2) ==
  \E d \in 0..(n-1) :
    (\A j \in 0..(d-1) : s1[j] = s2[j]) /\ s1[d] <= s2[d]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ n \in Nat
  /\ str \in [0..(n-1) -> CharacterSet]
  /\ f = [j \in 0..(2*n) |-> Sentinel]
  /\ k = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "OuterCheck"

\* ----------------------------------------------------------------------
\* Actions corresponding to the algorithm's labeled steps
\* ----------------------------------------------------------------------
OuterCheck ==
  /\ pc = "OuterCheck"
  /\ IF i < 2 * n THEN
        /\ pc' = "FailLookup"
        /\ UNCHANGED <<str, n, f, k, i, best>>
     ELSE
        /\ pc' = "Done"
        /\ UNCHANGED <<str, n, f, k, i, best>>

FailLookup ==
  /\ pc = "FailLookup"
  /\ /\ pos == (i + best) % n
     /\ k' = f[pos]
  /\ pc' = "InnerLoop"
  /\ UNCHANGED <<str, n, f, i, best>>

InnerLoop ==
  /\ pc = "InnerLoop"
  /\ curPos == i % n
  /\ candPos == (best + k) % n
  /\ curChar == str[curPos]
  /\ candChar == str[candPos]
  /\ IF curChar = candChar THEN
        /\ k' = k + 1
        /\ pc' = "InnerLoop"
        /\ UNCHANGED <<str, n, f, i, best>>
     ELSE IF k # Sentinel THEN
        /\ pc' = "FailLookup"   \* follow failure chain
        /\ UNCHANGED <<str, n, f, i, best, curChar, candChar>>
     ELSE
        /\ pc' = "PostComp"
        /\ UNCHANGED <<str, n, f, i, best, curChar, candChar>>

PostComp ==
  /\ pc = "PostComp"
  /\ curPos == i % n
  /\ candPos == (best + k) % n
  /\ curChar == str[curPos]
  /\ candChar == str[candPos]
  /\ IF curChar # candChar /\ curChar < candChar THEN
        /\ best' = i
        /\ f' = [j \in DOMAIN f |-> IF j = (i + best) % n THEN Sentinel ELSE f[j]]
        /\ pc' = "Increment"
        /\ UNCHANGED <<str, n, k, i>>
     ELSE
        /\ best' = best
        /\ f' = [j \in DOMAIN f |-> IF j = (i + best) % n THEN (k + 1) ELSE f[j]]
        /\ pc' = "Increment"
        /\ UNCHANGED <<str, n, k, i>>

Increment ==
  /\ pc = "Increment"
  /\ i' = i + 1
  /\ pc' = "OuterCheck"
  /\ UNCHANGED <<str, n, f, k, best>>

Done ==
  /\ pc = "Done"
  /\ UNCHANGED <<str, n, f, k, i, best, pc>>

Next ==
  \/ OuterCheck
  \/ FailLookup
  \/ InnerLoop
  \/ PostComp
  \/ Increment
  \/ Done

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<str, n, f, k, i, best, pc>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ n \in Nat
  /\ str \in [0..(n-1) -> CharacterSet]
  /\ f \in [0..(2*n) -> Int]
  /\ \A j \in DOMAIN f : f[j] = Sentinel \/ f[j] \in 0..n
  /\ k \in Int
  /\ i \in Nat
  /\ best \in 0..(n-1)
  /\ pc \in {"OuterCheck","FailLookup","InnerLoop","PostComp","Increment","Done"}

\* ----------------------------------------------------------------------
\* Correctness invariant (holds when algorithm terminates)
\* ----------------------------------------------------------------------
Correctness ==
  /\ pc = "Done"
  /\ \A shift \in 0..(n-1) :
        LexLe(Rot(str, best), Rot(str, shift))

====