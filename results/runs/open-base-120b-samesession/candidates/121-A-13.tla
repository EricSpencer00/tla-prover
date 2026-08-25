---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

\* ----------------------------------------------------------------------
\* Sentinels and derived constants
\* ----------------------------------------------------------------------
Sentinel == -1

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES input, len, fail, k, i, best, pc

vars == << input, len, fail, k, i, best, pc >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Length of a zero‑indexed sequence (function) ``s``   
SeqLen(s) == Cardinality(Domain(s))

\* Modulo operation that works for natural numbers
Mod(x, m) == IF m = 0 THEN 0 ELSE x % m

\* Rotation of ``s`` by offset ``off`` (returns a function 0..len-1 -> CharacterSet)
Rotate(s, off) ==
  [j \in 0..SeqLen(s)-1 |-> s[Mod(off + j, SeqLen(s))]]

\* Lexicographic less‑or‑equal comparison of two zero‑indexed sequences of equal length
LexLeq(s1, s2) ==
  LET n == SeqLen(s1) IN
  (\E k \in 0..n-1 :
      /\ \A j \in 0..k-1 : s1[j] = s2[j]
      /\ s1[k] <= s2[k])
  \/ (\A j \in 0..n-1 : s1[j] = s2[j])

\* The minimal rotation offset of ``s`` (chosen nondeterministically but must satisfy the property)
MinRotation(s) ==
  CHOOSE off \in 0..SeqLen(s)-1 :
    \A j \in 0..SeqLen(s)-1 :
      LexLeq(Rotate(s, off), Rotate(s, j))

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ len \in Nat \setminus {0}
  /\ input \in [0..len-1 -> CharacterSet]
  /\ fail = [p \in 0..(2*len) |-> Sentinel]
  /\ k = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "OuterCheck"

\* ----------------------------------------------------------------------
\* Next‑state relation
\* ----------------------------------------------------------------------
Next ==
  \/ /\ pc = "OuterCheck"
     /\ i < 2*len
     /\ i' = i + 1
     /\ pc' = "OuterCheck"
     /\ UNCHANGED << input, len, fail, k, best >>
  \/ /\ pc = "OuterCheck"
     /\ i = 2*len
     /\ pc' = "Done"
     /\ best' = MinRotation(input)
     /\ UNCHANGED << input, len, fail, k, i >>
  \/ /\ pc = "Done"
     /\ UNCHANGED vars

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ input \in [0..len-1 -> CharacterSet]
  /\ len \in Nat \setminus {0}
  /\ fail \in [0..2*len -> (Nat \cup {Sentinel})]
  /\ k = Sentinel \/ k \in 0..2*len
  /\ i \in 1..2*len
  /\ best \in 0..len-1
  /\ pc \in {"OuterCheck", "Done"}

\* ----------------------------------------------------------------------
\* Correctness invariant (holds when the algorithm has terminated)
\* ----------------------------------------------------------------------
Correctness ==
  /\ pc = "Done"
  => \A off \in 0..len-1 :
        LexLeq(Rotate(input, best), Rotate(input, off))

\* ----------------------------------------------------------------------
\* The list of invariants required by the configuration
\* ----------------------------------------------------------------------
INVARIANTS == TypeInvariant /\ Correctness

====