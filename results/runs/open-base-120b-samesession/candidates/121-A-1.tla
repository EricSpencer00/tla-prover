---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Integers, Sequences

CONSTANTS CharacterSet

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES str, n, fail, pi, i, best, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Sentinel == -1

\* Zero‑indexed string: a function from 0..n-1 to CharacterSet
String == [j \in 0..n-1 |-> str[j]]

\* Rotation of the string by offset o, represented as a zero‑indexed function
Rot(s, o) == [k \in 0..n-1 |-> s[(o + k) % n]]

\* Lexicographic less‑or‑equal between two zero‑indexed strings of equal length
LexLe(s, t) ==
  \A k \in 0..n-1 :
    ( \A j \in 0..k-1 : s[j] = t[j] ) => s[k] <= t[k]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ \E len \in Nat :
        /\ len > 0
        /\ str \in [0..len-1 -> CharacterSet]
        /\ n = len
  /\ fail = [j \in 0..2*n-1 |-> Sentinel]
  /\ pi   = Sentinel
  /\ i    = 1
  /\ best = 0
  /\ pc   = "Run"

\* ----------------------------------------------------------------------
\* Next-state relation (a simplified linear scan implementation)
\* ----------------------------------------------------------------------
Next ==
  \/ /\ pc = "Run"
     /\ i < 2 * n
     /\ LET a == str[i % n]
            b == str[(best + i) % n] IN
        /\ IF a < b
              THEN best' = i % n
              ELSE best' = best
        /\ i'    = i + 1
        /\ UNCHANGED <<str, n, fail, pi, pc>>
  \/ /\ pc = "Run"
     /\ i >= 2 * n
     /\ pc' = "Done"
     /\ UNCHANGED <<str, n, fail, pi, i, best>>
  \/ /\ pc = "Done"
     /\ UNCHANGED <<str, n, fail, pi, i, best, pc>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<str, n, fail, pi, i, best, pc>>

Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ str \in [0..n-1 -> CharacterSet]
  /\ n = Cardinality(DOMAIN str)
  /\ fail \in [0..2*n-1 -> Int]
  /\ pi \in Int
  /\ i \in Nat
  /\ best \in 0..n-1
  /\ pc \in {"Run", "Done"}
  /\ \A j \in DOMAIN fail : fail[j] = Sentinel \/ (fail[j] \in 0..2*n-1)

\* ----------------------------------------------------------------------
\* Correctness invariant (holds in the terminal state)
\* ----------------------------------------------------------------------
Correctness ==
  /\ pc = "Done"
  /\ \A off \in 0..n-1 :
        LexLe( Rot(str, best), Rot(str, off) )

\* ----------------------------------------------------------------------
\* Liveness: the algorithm eventually terminates
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

====