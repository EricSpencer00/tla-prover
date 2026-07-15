---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants
\* ----------------------------------------------------------------------
CONSTANTS CharacterSet, Nat

\* ----------------------------------------------------------------------
\* Types and helper definitions
\* ----------------------------------------------------------------------
Char == CharacterSet

Sentinel == -1

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES s,                 \* input string, a sequence of characters
          n,                 \* length of s
          f,                 \* failure function, a function from 0..2*n-1 to Sentinel or a valid index
          i,                 \* pattern-match index (can be Sentinel)
          j,                 \* outer loop counter, runs from 1 to 2*n
          best,              \* best rotation offset (0..n-1)
          pc                 \* program counter for labeled steps

\* ----------------------------------------------------------------------
\* Type invariant (used also as a safety invariant)
\* ----------------------------------------------------------------------
TypeOK ==
  /\ s \in Seq(Char)
  /\ n = Len(s)
  /\ n \in Nat
  /\ f \in [0 .. 2*n-1 -> (0..n-1) \cup {Sentinel}]
  /\ i \in (0..n-1) \cup {Sentinel}
  /\ j \in 0 .. 2*n
  /\ best \in 0 .. n-1
  /\ pc \in {"OuterCheck", "Lookup", "InnerLoop", "PostComp", "Terminate", "Stutter"}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ s \in Seq(Char)               \* nondeterministically chosen input string
  /\ n = Len(s)
  /\ f = [k \in 0..2*n-1 |-> Sentinel]
  /\ i = Sentinel
  /\ j = 1
  /\ best = 0
  /\ pc = "OuterCheck"

\* ----------------------------------------------------------------------
\* Helper functions
\* ----------------------------------------------------------------------
CharAt(pos) == s[ (pos % n) + 1 ]       \* zero‑indexed view: position 0 maps to element 1

RotateAt(off) == << CharAt(off + k) : k \in 0..n-1 >>   \* the rotation starting at offset off

\* ----------------------------------------------------------------------
\* Actions corresponding to labeled steps
\* ----------------------------------------------------------------------
OuterCheck ==
  /\ pc = "OuterCheck"
  /\ IF j >= 2*n
        THEN /\ pc' = "Terminate"
               /\ UNCHANGED << s, n, f, i, j, best >>
        ELSE /\ pc' = "Lookup"
             /\ UNCHANGED << s, n, f, i, j, best >>

Lookup ==
  /\ pc = "Lookup"
  /\ i' = f[ (j - best) % n ]
  /\ pc' = "InnerLoop"
  /\ UNCHANGED << s, n, f, j, best >>

InnerLoop ==
  /\ pc = "InnerLoop"
  /\ IF (CharAt(j) = CharAt(best + i + 1)) /\ i # Sentinel
        THEN /\ i' = i + 1
             /\ pc' = "InnerLoop"
        ELSE IF CharAt(j) = CharAt(best + i + 1)
                THEN /\ pc' = "PostComp"
             ELSE IF i = Sentinel
                THEN /\ pc' = "PostComp"
                ELSE /\ i' = i
                     /\ pc' = "PostComp"
  /\ UNCHANGED << s, n, f, j, best >>

PostComp ==
  /\ pc = "PostComp"
  /\ IF CharAt(j) # CharAt(best + i + 1) /\ i = Sentinel /\ CharAt(j) < CharAt(best + i + 1)
        THEN /\ best' = (j % n)
        ELSE /\ best' = best
  /\ IF CharAt(j) # CharAt(best + i + 1)
        THEN /\ f' = [f EXCEPT ![ (j - best) % n ] = i + 1]
        ELSE /\ f' = [f EXCEPT ![ (j - best) % n ] = Sentinel]
  /\ i' = f[ (j - best) % n ]          \* follow failure link for next iteration
  /\ j' = j + 1
  /\ pc' = "OuterCheck"
  /\ UNCHANGED s

Terminate ==
  /\ pc = "Terminate"
  /\ UNCHANGED << s, n, f, i, j, best, pc >>

Stutter ==
  /\ pc = "Stutter"
  /\ UNCHANGED << s, n, f, i, j, best, pc >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ OuterCheck
  \/ Lookup
  \/ InnerLoop
  \/ PostComp
  \/ (pc = "Terminate" /\ pc' = "Stutter" /\ UNCHANGED << s, n, f, i, j, best >>)
  \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<s, n, f, i, j, best, pc>>

\* ----------------------------------------------------------------------
\* Safety invariants required by the .cfg file
\* ----------------------------------------------------------------------
TypeInvariant == TypeOK

\* Correctness invariant: the rotation at 'best' is lexicographically minimal
Correctness ==
  /\ \A off \in 0..n-1 :
        RotateAt(best) <= RotateAt(off)

\* ----------------------------------------------------------------------
\* Liveness (optional, not required by the .cfg but kept for completeness)
\* ----------------------------------------------------------------------
Termination == <> (pc = "Terminate")

====