---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, FiniteSets

CONSTANTS CharacterSet

VARIABLES str, n, iPos, jPos, kPos, pc

\* ----------------------------------------------------------------------
\* Helper to obtain a character with circular indexing
Char(at) == str[at % n]

\* ----------------------------------------------------------------------
\* Initial state: nondeterministically choose a non‑empty string over
\* the given character set.
Init ==
    /\ n \in Nat \ {0}
    /\ str \in [0..n-1 -> CharacterSet]
    /\ iPos = 0
    /\ jPos = 1
    /\ kPos = 0
    /\ pc = "Loop"

\* ----------------------------------------------------------------------
\* Actions corresponding to Booth's algorithm
EqualStep ==
    /\ pc = "Loop"
    /\ iPos < n /\ jPos < n /\ kPos < n
    /\ Char(iPos + kPos) = Char(jPos + kPos)
    /\ iPos' = iPos
    /\ jPos' = jPos
    /\ kPos' = kPos + 1
    /\ pc'   = "Loop"
    /\ UNCHANGED str
    /\ UNCHANGED n

GreaterStep ==
    /\ pc = "Loop"
    /\ iPos < n /\ jPos < n /\ kPos < n
    /\ Char(iPos + kPos) > Char(jPos + kPos)
    /\ LET newi == iPos + kPos + 1 IN
          iPos' = IF newi <= jPos THEN jPos + 1 ELSE newi
    /\ jPos' = jPos
    /\ kPos' = 0
    /\ pc'   = "Loop"
    /\ UNCHANGED str
    /\ UNCHANGED n

LessStep ==
    /\ pc = "Loop"
    /\ iPos < n /\ jPos < n /\ kPos < n
    /\ Char(iPos + kPos) < Char(jPos + kPos)
    /\ LET newj == jPos + kPos + 1 IN
          jPos' = IF newj <= iPos THEN iPos + 1 ELSE newj
    /\ iPos' = iPos
    /\ kPos' = 0
    /\ pc'   = "Loop"
    /\ UNCHANGED str
    /\ UNCHANGED n

\* ----------------------------------------------------------------------
\* When the loop condition fails we move to the terminal state
DoneStep ==
    /\ pc = "Loop"
    /\ \lnot (iPos < n /\ jPos < n /\ kPos < n)
    /\ pc' = "Done"
    /\ UNCHANGED <<str, n, iPos, jPos, kPos>>

\* Stuttering after termination
Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<str, n, iPos, jPos, kPos, pc>>

Next == EqualStep \/ GreaterStep \/ LessStep \/ DoneStep \/ Stutter

vars == <<str, n, iPos, jPos, kPos, pc>>

Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
TypeInvariant ==
    /\ n \in Nat \ {0}
    /\ str \in [0..n-1 -> CharacterSet]
    /\ iPos \in Nat
    /\ jPos \in Nat
    /\ kPos \in Nat
    /\ pc \in {"Loop", "Done"}

\* ----------------------------------------------------------------------
\* Lexicographic less‑or‑equal between two rotations
LexLe(off1, off2) ==
    \E k \in 0..n-1 :
        ( \A l \in 0..k-1 :
            Char(off1 + l) = Char(off2 + l)
        )
        /\ Char(off1 + k) <= Char(off2 + k)
    \/ (\A l \in 0..n-1 : Char(off1 + l) = Char(off2 + l))

Best ==
    IF iPos < n /\ jPos < n THEN Min(iPos, jPos) ELSE Min(iPos, jPos)

\* Correctness: upon termination, Best yields the lexicographically
\* smallest rotation.
Correctness ==
    pc = "Done" =>
        \A off \in 0..n-1 : LexLe(Best, off)

====