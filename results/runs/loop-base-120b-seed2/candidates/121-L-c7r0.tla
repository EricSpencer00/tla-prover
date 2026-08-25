---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS CharacterSet

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES str, n, fail, k, i, best, pc

\* ----------------------------------------------------------------------
\* Definitions
\* ----------------------------------------------------------------------
Sentinel == -1

Steps == {"Check", "Lookup", "Inner", "Post", "Done"}

vars == <<str, n, fail, k, i, best, pc>>

\* Rotation of the string by offset off (zero‑based)
Rotation(off) == [j \in 0..(n-1) |-> str[(off + j) % n]]

\* Lexicographic less‑or‑equal between two zero‑indexed sequences of length n
LexLe(s1, s2) ==
  \A j \in 0..(n-1) :
    ( \A k \in 0..(j-1) : s1[k] = s2[k] ) => s1[j] <= s2[j]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ n \in Nat
  /\ n > 0
  /\ str \in [0..(n-1) -> CharacterSet]
  /\ fail = [j \in 0..(2*n-1) |-> Sentinel]
  /\ k = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "Check"

\* ----------------------------------------------------------------------
\* Actions corresponding to the algorithm steps
\* ----------------------------------------------------------------------
CheckContinue ==
  /\ pc = "Check"
  /\ i < 2 * n
  /\ pc' = "Lookup"
  /\ UNCHANGED <<str, n, fail, k, i, best>>

CheckTerminate ==
  /\ pc = "Check"
  /\ i >= 2 * n
  /\ pc' = "Done"
  /\ UNCHANGED <<str, n, fail, k, i, best>>

LookupAction ==
  /\ pc = "Lookup"
  /\ k' = fail[i]
  /\ pc' = "Inner"
  /\ UNCHANGED <<str, n, fail, i, best>>

InnerEqual ==
  /\ pc = "Inner"
  /\ k # Sentinel
  /\ str[i % n] = str[(best + k) % n]
  /\ k' = k + 1
  /\ pc' = "Inner"
  /\ UNCHANGED <<str, n, fail, i, best>>

InnerMismatch ==
  /\ pc = "Inner"
  /\ (k = Sentinel) \/ (str[i % n] # str[(best + k) % n])
  /\ pc' = "Post"
  /\ UNCHANGED <<str, n, fail, i, best, k>>

PostAction ==
  /\ pc = "Post"
  /\ LET cur  == str[i % n] 
         cand == IF k = Sentinel THEN str[best % n] ELSE str[(best + k) % n] IN
     /\ IF cur # cand /\ cur < cand
          THEN best' = i % n
          ELSE best' = best
  /\ fail' = [fail EXCEPT ![i] = IF cur # cand THEN Sentinel ELSE k + 1]
  /\ i' = i + 1
  /\ pc' = "Check"
  /\ UNCHANGED <<str, n, k>>

Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  \/ CheckContinue
  \/ CheckTerminate
  \/ LookupAction
  \/ InnerEqual
  \/ InnerMismatch
  \/ PostAction
  \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ str \in [0..(n-1) -> CharacterSet]
  /\ n \in Nat
  /\ n > 0
  /\ fail \in [0..(2*n-1) -> (Sentinel \cup 0..(2*n-1))]
  /\ k \in (Sentinel) \cup 0..(2*n-1)
  /\ i \in Nat
  /\ i >= 1
  /\ best \in 0..(n-1)
  /\ pc \in Steps

Correctness ==
  /\ pc = "Done"
  /\ \A shift \in 0..(n-1) : LexLe(Rotation(best), Rotation(shift))

\* ----------------------------------------------------------------------
\* The required identifiers for the .cfg file
\* ----------------------------------------------------------------------
CONSTANT CharacterSet
SPECIFICATION Spec
INVARIANT TypeInvariant
INVARIANT Correctness

====