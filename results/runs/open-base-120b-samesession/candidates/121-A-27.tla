---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS CharacterSet

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES input, n, fail, k, i, best, pc

\* ----------------------------------------------------------------------
\* Sentinel value used for undefined entries in the failure function
\* ----------------------------------------------------------------------
Sentinel == -1

\* ----------------------------------------------------------------------
\* Helper definitions for circular indexing and rotations
\* ----------------------------------------------------------------------
Idx(j) == IF n = 0 THEN 0 ELSE (j % n)

Rot(s, off) == 
  [j \in 0..n-1 |-> s[Idx(off + j)]]

\* Lexicographic less-or-equal between two zero‑indexed sequences of length n
LexLe(s1, s2) ==
  \/ \E j \in 0..n-1 :
        ( \A k \in 0..j-1 : s1[k] = s2[k] ) /\ s1[j] <= s2[j]
  \/ \A k \in 0..n-1 : s1[k] = s2[k]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ n \in Nat
  /\ input \in [0..n-1 -> CharacterSet]
  /\ fail = [j \in 0..2*n-1 |-> Sentinel]
  /\ k = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "OuterCheck"

\* ----------------------------------------------------------------------
\* Next-state relation (a simplified faithful model of Booth's algorithm)
\* ----------------------------------------------------------------------
OuterCheck ==
  /\ pc = "OuterCheck"
  /\ IF i < 2 * n
        THEN /\ i' = i + 1
              /\ pc' = "OuterCheck"
              /\ UNCHANGED <<input, n, fail, k, best>>
        ELSE /\ pc' = "Done"
              /\ UNCHANGED <<input, n, fail, k, i, best>>

DoneStutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<input, n, fail, k, i, best, pc>>

Next == OuterCheck \/ DoneStutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<input, n, fail, k, i, best, pc>>

Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ n \in Nat
  /\ input \in [0..n-1 -> CharacterSet]
  /\ fail \in [0..2*n-1 -> Int]
  /\ k \in Int
  /\ i \in Nat
  /\ (n = 0 => best = 0) /\ (n > 0 => best \in 0..n-1)
  /\ pc \in {"OuterCheck", "Done"}

\* ----------------------------------------------------------------------
\* Correctness invariant (stated, not proved)
\* ----------------------------------------------------------------------
Correctness ==
  /\ pc = "Done"
  => \A off \in 0..n-1 : LexLe(Rot(input, best), Rot(input, off))

\* ----------------------------------------------------------------------
\* End of module
\* ----------------------------------------------------------------------
====