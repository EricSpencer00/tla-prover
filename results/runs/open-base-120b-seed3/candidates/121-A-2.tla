---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences

CONSTANTS
    CharacterSet \* a finite subset of Nat, supplied by the model checker

\* ----------------------------------------------------------------------
\* Sentinel value for undefined indices in the failure function
\* ----------------------------------------------------------------------
Sentinel == -1

\* ----------------------------------------------------------------------
\* Program counter values
\* ----------------------------------------------------------------------
PCVals == {"OuterCheck", "Lookup", "InnerLoop", "PostComp", "Done"}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    str,    \* input string: function [0..n-1 -> CharacterSet]
    n,      \* length of the string
    fail,   \* failure function: function [0..2*n-1 -> Nat \cup {Sentinel}]
    i,      \* pattern‑match index (may be Sentinel)
    k,      \* outer loop counter
    best,   \* offset of the best rotation found so far
    pc      \* program counter, one of PCVals

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Idx(j) == (best + j) % n   \* index into the circular string

RotSeq(off) == << str[(off + j) % n] : j \in 0..n-1 >>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ n \in Nat
    /\ str \in [0..n-1 -> CharacterSet]
    /\ fail = [j \in 0..2*n-1 |-> Sentinel]
    /\ i = Sentinel
    /\ k = 1
    /\ best = 0
    /\ pc = "OuterCheck"

\* ----------------------------------------------------------------------
\* Next‑state relation
\* ----------------------------------------------------------------------
Next ==
\/ /\ pc = "OuterCheck"
   /\ IF k < 2 * n
        THEN /\ pc' = "Lookup"
             /\ UNCHANGED <<str, n, fail, i, best, k>>
        ELSE /\ pc' = "Done"
             /\ UNCHANGED <<str, n, fail, i, best, k>>
\/ /\ pc = "Lookup"
   /\ i' = fail[Idx(k)]
   /\ pc' = "InnerLoop"
   /\ UNCHANGED <<str, n, fail, best, k>>
\/ /\ pc = "InnerLoop"
   LET cur  == Idx(k)
       cand == Idx(i)
   IN
   IF i # Sentinel /\ str[cur] = str[cand] THEN
        /\ i' = i + 1
        /\ pc' = "InnerLoop"
        /\ UNCHANGED <<str, n, fail, best, k>>
   ELSE
        IF i # Sentinel /\ str[cur] > str[cand] THEN
            /\ best' = cur
            /\ i' = Sentinel
        ELSE
            /\ i' = Sentinel
        /\ pc' = "PostComp"
        /\ UNCHANGED <<str, n, fail, k>>
\/ /\ pc = "PostComp"
   /\ fail' = [fail EXCEPT ![Idx(k)] = IF i = Sentinel THEN Sentinel ELSE i + 1]
   /\ k' = k + 1
   /\ pc' = "OuterCheck"
   /\ UNCHANGED <<str, n, best, i>>
\/ /\ pc = "Done"
   /\ UNCHANGED <<str, n, fail, i, best, k, pc>>

\* ----------------------------------------------------------------------
\* Variables tuple for the action operator
\* ----------------------------------------------------------------------
vars == <<str, n, fail, i, best, k, pc>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ n \in Nat
    /\ str \in [0..n-1 -> CharacterSet]
    /\ fail \in [0..2*n-1 -> Nat \cup {Sentinel}]
    /\ i \in Nat \cup {Sentinel}
    /\ k \in Nat
    /\ (n = 0 => best = 0) /\ (n > 0 => best \in 0..n-1)
    /\ pc \in PCVals

\* ----------------------------------------------------------------------
\* Correctness property (lexicographically minimal rotation)
\* ----------------------------------------------------------------------
Correctness ==
    /\ pc = "Done"
    /\ \A off \in 0..n-1 :
          RotSeq(best) <= RotSeq(off)
    /\ \A off \in 0..n-1 :
          (RotSeq(best) = RotSeq(off) => best <= off)

\* ----------------------------------------------------------------------
\* TLC configuration placeholders (required identifiers)
\* ----------------------------------------------------------------------
\* The .cfg file will supply the value of CharacterSet
\* and may bound n via model checking options.

====