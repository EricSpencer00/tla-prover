---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets

\*=====================================================================
\* Constants
\*=====================================================================
CONSTANTS 
    CharacterSet      \* Finite subset of Nat (defined below)

\*=====================================================================
\* Finite version of Nat for the character set
\*=====================================================================
\* The .cfg file will replace occurrences of Nat with this operator.
CharacterSet == 0..10      \* example finite alphabet; can be overridden in the cfg

\*=====================================================================
\* State variables
\*=====================================================================
VARIABLES 
    str,        \* input string, a function from 0..n-1 to CharacterSet
    n,          \* length of the input string
    fail,       \* failure function array indexed 0..2*n-1
    p,          \* pattern‑match index (may be the sentinel)
    i,          \* outer loop counter, runs from 1 up to 2*n
    best,       \* current best rotation offset (0..n-1)
    pc          \* program counter (one of the labelled steps)

\*=====================================================================
\* Constants used internally
\*=====================================================================
Sentinel == -1

\*=====================================================================
\* Helper definitions
\*=====================================================================
Char(pos) == 
    /\ n > 0
    /\ LET idx == pos % n IN str[idx]

RotSeq(off) == 
    /\ n > 0
    /\ << Char(off + k) : k \in 0..n-1 >>

LexLe(s, t) == 
    /\ Len(s) = Len(t)
    /\ IF Len(s) = 0 THEN TRUE
       ELSE IF Head(s) < Head(t) THEN TRUE
            ELSE IF Head(s) > Head(t) THEN FALSE
                 ELSE LexLe(Tail(s), Tail(t))

\*=====================================================================
\* Initialization
\*=====================================================================
Init ==
    /\ n \in Nat \ {0}
    /\ str \in [0..n-1 -> CharacterSet]
    /\ fail = [j \in 0..2*n-1 |-> Sentinel]
    /\ p = Sentinel
    /\ i = 1
    /\ best = 0
    /\ pc = "OuterCheck"

\*=====================================================================
\* Action definitions (one step of the algorithm)
\*=====================================================================
OuterCheck ==
    /\ pc = "OuterCheck"
    /\ IF i < 2 * n 
          THEN /\ pc' = "Lookup"
               /\ UNCHANGED << str, n, fail, p, i, best >>
          ELSE /\ pc' = "Done"
               /\ UNCHANGED << str, n, fail, p, i, best >>

Lookup ==
    /\ pc = "Lookup"
    /\ LET pos == (i + best) % (2 * n) IN
       /\ p' = fail[pos]
    /\ pc' = "InnerLoop"
    /\ UNCHANGED << str, n, fail, i, best >>

InnerLoop ==
    /\ pc = "InnerLoop"
    /\ LET curChar == Char(i)
           candIdx == (best + p + 1) % n
           candChar == Char(candIdx) IN
       IF curChar = candChar
          THEN /\ p' = p + 1
               /\ pc' = "InnerLoop"    \* continue comparing
          ELSE IF curChar # candChar
               THEN /\ IF curChar < candChar 
                         THEN best' = i % n
                     ELSE UNCHANGED best
                    /\ p' = Sentinel
                    /\ pc' = "PostCompare"
               ELSE UNCHANGED << p, best, pc >>
    /\ UNCHANGED << str, n, fail, i >>

PostCompare ==
    /\ pc = "PostCompare"
    /\ LET curChar == Char(i)
           candIdx == (best + p + 1) % n
           candChar == Char(candIdx) IN
       /\ IF p = Sentinel 
            THEN IF curChar < candChar 
                     THEN best' = i % n
                     ELSE UNCHANGED best
                 ELSE UNCHANGED best
       /\ fail' = [fail EXCEPT ![(i + best) % (2 * n)] = 
                     IF p = Sentinel THEN Sentinel ELSE p + 1]
       /\ pc' = "IncI"
       /\ UNCHANGED << str, n, p, i >>

IncI ==
    /\ pc = "IncI"
    /\ i' = i + 1
    /\ pc' = "OuterCheck"
    /\ UNCHANGED << str, n, fail, p, best >>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED << str, n, fail, p, i, best, pc >>

\*=====================================================================
\* Next-state relation
\*=====================================================================
Next == 
    \/ OuterCheck
    \/ Lookup
    \/ InnerLoop
    \/ PostCompare
    \/ IncI
    \/ Done

\*=====================================================================
\* Specification
\*=====================================================================
Spec == Init /\ [][Next]_<<str, n, fail, p, i, best, pc>>

\*=====================================================================
\* Type invariant
\*=====================================================================
TypeInvariant ==
    /\ n \in Nat \ {0}
    /\ str \in [0..n-1 -> CharacterSet]
    /\ fail \in [0..2*n-1 -> (Sentinel \cup Nat)]
    /\ p \in Sentinel \cup Nat
    /\ i \in Nat
    /\ best \in 0..n-1
    /\ pc \in {"OuterCheck","Lookup","InnerLoop","PostCompare","IncI","Done"}

\*=====================================================================
\* Correctness property
\*=====================================================================
Correctness ==
    /\ pc = "Done"
    /\ \A off \in 0..n-1 :
          LexLe(RotSeq(best), RotSeq(off))

\*=====================================================================
\* The properties required by the .cfg file
\*=====================================================================
INVARIANT TypeInvariant
INVARIANT Correctness

====