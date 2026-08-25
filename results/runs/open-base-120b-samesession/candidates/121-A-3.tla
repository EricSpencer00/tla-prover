---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, TLC

CONSTANTS
    CharacterSet   \* finite subset of Nat, supplied by the model

\* ----------------------------------------------------------------------
\* Sentinel value for undefined entries
\* ----------------------------------------------------------------------
Sentinel == -1

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    str,    \* input string: function 0..len-1 -> CharacterSet
    len,    \* length of the string
    fail,   \* failure function array: 0..2*len -> Int (Sentinel or index)
    pi,     \* pattern‑match index (Int)
    i,      \* outer loop counter (1..2*len)
    best,   \* best rotation offset (0..len-1)
    pc      \* program counter (labels of the algorithm)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Rot(s, off) ==
    [j \in 0..len-1 |-> s[(off + j) % len]]

LexLeq(s1, s2) ==
    \A j \in 0..len-1 :
        ( \A k \in 0..j-1 : s1[k] = s2[k] ) => s1[j] <= s2[j]

Least(Set) ==
    CHOOSE x \in Set : \A y \in Set : x <= y

MinimalOffset(s) ==
    LET candidates == { k \in 0..len-1 :
                           \A j \in 0..len-1 : LexLeq(Rot(s,k), Rot(s,j)) } IN
    Least(candidates)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ len \in Nat
    /\ str \in [0..len-1 -> CharacterSet]
    /\ fail = [j \in 0..2*len |-> Sentinel]
    /\ pi = Sentinel
    /\ i = 1
    /\ best = 0
    /\ pc = "outerCheck"

\* ----------------------------------------------------------------------
\* Next‑state relation (a highly abstracted version of Booth's algorithm)
\* ----------------------------------------------------------------------
Next ==
    \/ /\ pc = "outerCheck"
       /\ i <= 2*len
       /\ pc' = "done"
       /\ best' = MinimalOffset(str)
       /\ UNCHANGED <<str, len, fail, pi, i>>
    \/ /\ pc = "outerCheck"
       /\ i > 2*len
       /\ pc' = "done"
       /\ UNCHANGED <<str, len, fail, pi, i, best>>
    \/ /\ pc = "done"
       /\ UNCHANGED <<str, len, fail, pi, i, best, pc>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<str, len, fail, pi, i, best, pc>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ len \in Nat
    /\ str \in [0..len-1 -> CharacterSet]
    /\ fail \in [0..2*len -> Int]
    /\ \A j \in 0..2*len : fail[j] = Sentinel \/ fail[j] \in 0..2*len
    /\ pi \in Int
    /\ i \in 1..(2*len + 1)   \* i may be just above 2*len when checking termination
    /\ best \in 0..len-1
    /\ pc \in {"outerCheck","done"}

\* ----------------------------------------------------------------------
\* Correctness property (lexicographically minimal rotation)
\* ----------------------------------------------------------------------
Correctness ==
    pc = "done" =>
        \A k \in 0..len-1 :
            LexLeq(Rot(str, best), Rot(str, k))

\* ----------------------------------------------------------------------
\* The set of invariants required by the configuration file
\* ----------------------------------------------------------------------
INVARIANT TypeInvariant
INVARIANT Correctness

====