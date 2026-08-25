---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS CharacterSet

\* ----------------------------------------------------------------------
\* Definitions
\* ----------------------------------------------------------------------
Sentinel == -1

\* Length of a sequence (zero‑indexed)
Len(s) == IF DOMAIN s = {} THEN 0 ELSE (Max(DOMAIN s) + 1)

\* Modulo operation for natural numbers
Mod(i, m) == IF m = 0 THEN 0 ELSE i % m

\* Rotation of the string s by offset o (produces a sequence of length n)
Rotation(s, o) ==
  LET n == Len(s) IN
    [j \in 0..n-1 |-> s[Mod(o + j, n)]]

\* Lexicographic “less‑than” on two rotations of equal length
LexLess(x, y) ==
  \E k \in DOMAIN x :
    /\ \A l \in 0..k-1 : x[l] = y[l]
    /\ x[k] < y[k]

LexLe(x, y) == (x = y) \/ LexLess(x, y)

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES s, fail, pIdx, i, best, pc

\* Set of all variables (used in the temporal formula)
vars == << s, fail, pIdx, i, best, pc >>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ s \in [0..] -> CharacterSet          \* nondeterministic string
  /\ Len(s) = Len(s)                     \* just to bind Len(s) early
  /\ n == Len(s)
  /\ fail = [j \in 0..2*n-1 |-> Sentinel]
  /\ pIdx = Sentinel
  /\ i = 1
  /\ best = 0
  /\ pc = "OuterCheck"

\* ----------------------------------------------------------------------
\* Next-state relation (abstracted version of Booth’s algorithm)
\* ----------------------------------------------------------------------
OuterCheck ==
  /\ pc = "OuterCheck"
  /\ n == Len(s)
  /\ IF i < 2 * n
       THEN /\ pc' = "Lookup"
            /\ UNCHANGED << s, fail, pIdx, best >>
       ELSE /\ pc' = "Done"
            /\ UNCHANGED << s, fail, pIdx, i, best >>
  /\ i' = i

Lookup ==
  /\ pc = "Lookup"
  /\ pc' = "Inc"
  /\ UNCHANGED << s, fail, pIdx, i, best >>

Inc ==
  /\ pc = "Inc"
  /\ i' = i + 1
  /\ pc' = "OuterCheck"
  /\ UNCHANGED << s, fail, pIdx, best >>

Done ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  \/ OuterCheck
  \/ Lookup
  \/ Inc
  \/ Done
  \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ s \in [0..] -> CharacterSet
  /\ n == Len(s)
  /\ n \in Nat
  /\ fail \in [0..2*n-1 -> (Nat \cup {Sentinel})]
  /\ pIdx \in (Nat \cup {Sentinel})
  /\ i \in Nat
  /\ best \in 0..(n-1) \/ (n = 0)   \* when n = 0, best is irrelevant
  /\ pc \in {"OuterCheck", "Lookup", "Inc", "Done"}

\* ----------------------------------------------------------------------
\* Correctness property (lexicographically minimal rotation)
\* ----------------------------------------------------------------------
Correctness ==
  /\ pc = "Done"
  /\ \A off \in 0..(Len(s)-1) :
        LET rBest == Rotation(s, best)
            rOff  == Rotation(s, off) IN
          LexLe(rBest, rOff)

\* ----------------------------------------------------------------------
\* Liveness: termination (optional, expressed as a temporal property)
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

====