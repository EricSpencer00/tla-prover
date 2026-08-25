---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets, ZSequences

CONSTANTS CharacterSet

\* ----------------------------------------------------------------------
\*  Parameters
\* ----------------------------------------------------------------------
Sentinel == -1

\* ----------------------------------------------------------------------
\*  State variables
\* ----------------------------------------------------------------------
VARIABLES str,              \* input string (sequence of characters)
          n,                \* length of the input string
          fail,             \* failure function array 0..2*n-1 -> Nat \cup {Sentinel}
          pi,               \* pattern‑match index (current failure lookup)
          i,                \* outer loop counter, runs from 1 to 2*n
          best,             \* best rotation offset found so far
          pc                \* program counter (identifies the current step)

vars == << str, n, fail, pi, i, best, pc >>

\* ----------------------------------------------------------------------
\*  Helper definitions
\* ----------------------------------------------------------------------
CharAt(pos) == str[ pos % n ]

Rot(s, off) == << s[(j + off) % Len(s)] : j \in 0..Len(s)-1 >>

\* ----------------------------------------------------------------------
\*  Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ str \in Seq(CharacterSet)                \* any finite sequence over the alphabet
    /\ n = Len(str)
    /\ n > 0                                    \* we consider only non‑empty strings
    /\ fail = [j \in 0..2*n-1 |-> Sentinel]    \* all entries undefined
    /\ pi = Sentinel
    /\ i = 1
    /\ best = 0
    /\ pc = "Check"

\* ----------------------------------------------------------------------
\*  Algorithmic steps (each step corresponds to a labelled program point)
\* ----------------------------------------------------------------------
Check ==
    /\ pc = "Check"
    /\ IF i < 2 * n
       THEN /\ pc' = "Lookup"
            /\ UNCHANGED << str, n, fail, pi, i, best >>
       ELSE /\ pc' = "Done"
            /\ UNCHANGED << str, n, fail, pi, i, best >>

Lookup ==
    /\ pc = "Lookup"
    /\ let idx == (i - best) % (2 * n) in
       pi' = IF idx \in DOMAIN fail THEN fail[idx] ELSE Sentinel
    /\ pc' = "Compare"
    /\ UNCHANGED << str, n, fail, i, best >>

Compare ==
    /\ pc = "Compare"
    /\ LET c1 == CharAt(i) IN
       LET c2 == CharAt((best + pi + 1) % n) IN
       IF c1 = c2
          THEN /\ pi' = pi + 1
               /\ pc' = "Compare"
               /\ UNCHANGED << str, n, fail, i, best >>
          ELSE /\ pc' = "PostComp"
               /\ UNCHANGED << str, n, fail, i, best, pi >>

PostComp ==
    /\ pc = "PostComp"
    /\ LET c1 == CharAt(i) IN
       LET c2 == CharAt((best + pi + 1) % n) IN
       /\ IF c1 # c2 /\ pi = Sentinel
          THEN /\ IF c1 < c2
                THEN best' = (i - pi - 1) % n
                ELSE best' = best
                /\ fail' = [fail EXCEPT ![(i - best) % (2*n)] = Sentinel]
          ELSE /\ IF c1 < c2
                THEN best' = (i - pi - 1) % n
                ELSE best' = best
                /\ fail' = [fail EXCEPT ![(i - best) % (2*n)] = pi + 1]
    /\ pi' = fail[(i - best) % (2*n)]
    /\ pc' = "Inc"
    /\ UNCHANGED i

Inc ==
    /\ pc = "Inc"
    /\ i' = i + 1
    /\ pc' = "Check"
    /\ UNCHANGED << str, n, fail, pi, best >>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Check
    \/ Lookup
    \/ Compare
    \/ PostComp
    \/ Inc
    \/ Done
    \/ Stutter

\* ----------------------------------------------------------------------
\*  Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\*  Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ str \in Seq(CharacterSet)
    /\ n = Len(str)
    /\ n > 0
    /\ fail \in [0..2*n-1 -> (0..n) \cup {Sentinel}]
    /\ pi \in (0..n) \cup {Sentinel}
    /\ i \in 1..(2*n)
    /\ best \in 0..n-1
    /\ pc \in {"Check","Lookup","Compare","PostComp","Inc","Done"}

\* ----------------------------------------------------------------------
\*  Correctness invariant (holds when the algorithm terminates)
\* ----------------------------------------------------------------------
Correctness ==
    /\ pc = "Done"
    /\ \A off \in 0..n-1 :
          Rot(str, best) <= Rot(str, off)

\* ----------------------------------------------------------------------
\*  Liveness property (termination)
\* ----------------------------------------------------------------------
Termination == <>[](pc = "Done")

\* ----------------------------------------------------------------------
\*  The set of invariants for the model checker
\* ----------------------------------------------------------------------
INVARIANTS == TypeInvariant, Correctness

\* ----------------------------------------------------------------------
\*  The specification that the model checker must verify
\* ----------------------------------------------------------------------
SPECIFICATION == Spec

====