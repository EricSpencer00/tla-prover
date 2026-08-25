---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, TLC

CONSTANTS CharacterSet

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES str, n, fail, k, i, best, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Sentinel == -1

Idx(j) == (best + j) % (2 * n)

CharAt(pos) == str[pos % n]

Rot(offset) ==
  [p \in 0..(n-1) |-> str[(offset + p) % n]]

LexLe(s1, s2) ==
  \E p \in 0..(n-1) :
    ( \A q \in 0..(p-1) : s1[q] = s2[q] )
    /\ s1[p] < s2[p]
  \/ (\A q \in 0..(n-1) : s1[q] = s2[q])

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ n \in Nat
  /\ str \in [0..(n-1) -> CharacterSet]
  /\ fail = [j \in 0..(2 * n) |-> Sentinel]
  /\ k = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "OuterCheck"

\* ----------------------------------------------------------------------
\* Actions (one for each program‑counter label)
\* ----------------------------------------------------------------------
OuterCheck ==
  /\ pc = "OuterCheck"
  /\ IF i < 2 * n
        THEN /\ pc' = "Lookup"
             /\ UNCHANGED <<str, n, fail, k, i, best>>
        ELSE /\ pc' = "Done"
             /\ UNCHANGED <<str, n, fail, k, i, best>>

Lookup ==
  /\ pc = "Lookup"
  /\ k' = fail[Idx(i)]
  /\ pc' = "InnerLoop"
  /\ UNCHANGED <<str, n, fail, i, best>>

InnerLoop ==
  /\ pc = "InnerLoop"
  /\ LET a == CharAt(i) 
         b == CharAt(best + i) IN
     IF a = b
        THEN /\ pc' = "Inc"
             /\ UNCHANGED <<str, n, fail, k, i, best>>
     ELSE IF k # Sentinel
        THEN /\ pc' = "FollowFail"
             /\ UNCHANGED <<str, n, fail, i, best>>
     ELSE /\ pc' = "PostComp"
          /\ UNCHANGED <<str, n, fail, i, best>>

FollowFail ==
  /\ pc = "FollowFail"
  /\ k' = fail[Idx(i)]
  /\ pc' = "InnerLoop"
  /\ UNCHANGED <<str, n, fail, i, best>>

PostComp ==
  /\ pc = "PostComp"
  /\ LET a == CharAt(i)
         b == CharAt(best + i)
         idx == Idx(i) IN
     /\ IF a # b /\ a < b
           THEN best' = i % n
           ELSE best' = best
     /\ IF a # b
           THEN fail' = [fail EXCEPT ![idx] = Sentinel]
           ELSE fail' = [fail EXCEPT ![idx] = k + 1]
     /\ pc' = "Inc"
     /\ UNCHANGED <<str, n, i, k>>

Inc ==
  /\ pc = "Inc"
  /\ i' = i + 1
  /\ pc' = "OuterCheck"
  /\ UNCHANGED <<str, n, fail, k, best>>

Done ==
  /\ pc = "Done"
  /\ pc' = "Done"
  /\ UNCHANGED <<str, n, fail, k, i, best>>

\* Stuttering when terminated
Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<str, n, fail, k, i, best, pc>>

Next ==
  \/ OuterCheck
  \/ Lookup
  \/ InnerLoop
  \/ FollowFail
  \/ PostComp
  \/ Inc
  \/ Done
  \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<str, n, fail, k, i, best, pc>>

Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ n \in Nat
  /\ str \in [0..(n-1) -> CharacterSet]
  /\ fail \in [0..(2 * n) -> Int]
  /\ \A j \in DOMAIN fail : fail[j] = Sentinel \/ fail[j] \in 0..(2 * n)
  /\ k \in Int
  /\ i \in Nat
  /\ best \in 0..(n-1)
  /\ pc \in {"OuterCheck","Lookup","InnerLoop","FollowFail","PostComp","Inc","Done"}

Correctness ==
  (pc = "Done") =>
    \A j \in 0..(n-1) : LexLe(Rot(best), Rot(j))

\* ----------------------------------------------------------------------
\* The required identifiers for the .cfg file
\* ----------------------------------------------------------------------
SPECIFICATION == Spec
INVARIANTS == TypeInvariant, Correctness

====