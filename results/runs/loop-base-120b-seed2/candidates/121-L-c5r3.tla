---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, ZSequences

\* ----------------------------------------------------------------------
\* Finite character set (replaces [ZSequences]CharacterSet)
\* ----------------------------------------------------------------------
CONSTANT CharacterSet

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES str, n, i, j, k, best, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Max(a, b) == IF a > b THEN a ELSE b
Min(a, b) == IF a < b THEN a ELSE b

Rotation(off) ==
    << str[(off + t) % n] : t \in 0..(n-1) >>

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ str \in Seq(CharacterSet)
    /\ n = Len(str)
    /\ i = 0
    /\ j = 1
    /\ k = 0
    /\ best = 0
    /\ pc = "Run"

\* ----------------------------------------------------------------------
\* Next-state relation (implementation of Booth's algorithm)
\* ----------------------------------------------------------------------
Next ==
    \/ /\ pc = "Run"
       /\ IF i < n /\ j < n THEN
            LET a == str[(i + k) % n]
                b == str[(j + k) % n]
            IN IF a = b THEN
                   /\ k' = k + 1
                   /\ UNCHANGED << str, n, i, j, best, pc >>
               ELSE IF a > b THEN
                   /\ i' = Max(i + k + 1, j + 1)
                   /\ k' = 0
                   /\ UNCHANGED << str, n, j, best, pc >>
               ELSE
                   /\ j' = Max(j + k + 1, i + 1)
                   /\ k' = 0
                   /\ UNCHANGED << str, n, i, best, pc >>
          ELSE
               /\ best' = Min(i, j)
               /\ pc' = "Done"
               /\ UNCHANGED << str, n, i, j, k >>
    \/ /\ pc = "Done"
       /\ UNCHANGED << str, n, i, j, k, best, pc >>

\* ----------------------------------------------------------------------
\* Variables tuple for temporal operators
\* ----------------------------------------------------------------------
vars == << str, n, i, j, k, best, pc >>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ str \in Seq(CharacterSet)
    /\ n = Len(str)
    /\ i \in 0..n
    /\ j \in 0..n
    /\ k \in Nat
    /\ best \in 0..(Max(1, n) - 1)   \* best is a valid offset when n>0
    /\ pc \in {"Run", "Done"}

\* ----------------------------------------------------------------------
\* Correctness property (lexicographically minimal rotation)
\* ----------------------------------------------------------------------
Correctness ==
    /\ pc = "Done"
    /\ \A off \in 0..(n-1) : Rotation(best) \preceq Rotation(off)

====