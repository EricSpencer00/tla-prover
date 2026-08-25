---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Integers

CONSTANTS
    CharacterSet

\* Sentinel value used for undefined failure‑function entries
SENTINEL == -1

\* State variables
VARIABLES
    s,          \* input string: function [0..n-1 -> CharacterSet]
    n,          \* length of the input string
    f,          \* failure function array (unused but present)
    i,          \* index i of Booth's algorithm
    j,          \* index j of Booth's algorithm
    k,          \* length of current match
    best,       \* best rotation offset found so far
    pc          \* program counter (label of the current step)

\* Helper: character at a (possibly wrapped) position
CharAt(pos) ==
    IF n = 0 THEN SENTINEL
    ELSE s[(pos) % n]

\* Helper: lexicographic less‑or‑equal between two rotations
Rotation(off) ==
    [p \in 0..n-1 |-> CharAt(off + p)]

LexLe(rot1, rot2) ==
    \A p \in 0..n-1 :
        IF rot1[p] # rot2[p] THEN rot1[p] < rot2[p] ELSE TRUE

\* Type invariant for all reachable states
TypeInvariant ==
    /\ n \in Nat
    /\ IF n = 0 THEN s = {} ELSE s \in [0..n-1 -> CharacterSet]
    /\ f \in [0..2*n -> Int]               \* each entry is an integer (sentinel or index)
    /\ i \in Nat
    /\ j \in Nat
    /\ k \in Nat
    /\ best \in 0..(IF n = 0 THEN 0 ELSE n-1)
    /\ pc \in {"Check", "Compare", "Done"}

\* Correctness: when the algorithm terminates, the rotation at 'best'
\* is lexicographically minimal among all rotations
Correctness ==
    /\ pc = "Done"
    /\ \A off \in 0..(IF n = 0 THEN 0 ELSE n-1) :
          LexLe(Rotation(best), Rotation(off))

\* Initial state: nondeterministically choose a string of length n
Init ==
    /\ n \in Nat
    /\ s = IF n = 0 THEN {} ELSE
           [p \in 0..n-1 |-> CHOOSE c \in CharacterSet : TRUE]
    /\ f = [p \in 0..2*n |-> SENTINEL]
    /\ i = 0
    /\ j = 1
    /\ k = 0
    /\ best = 0
    /\ pc = "Check"

\* Transition that checks whether the main loop should continue
Check ==
    /\ pc = "Check"
    /\ IF (i < n) /\ (j < n)
          THEN /\ pc' = "Compare"
               /\ UNCHANGED <<s, n, f, i, j, k, best>>
          ELSE /\ best' = IF i <= j THEN i ELSE j
               /\ pc' = "Done"
               /\ UNCHANGED <<s, n, f, i, j, k>>

\* Core comparison step of Booth's algorithm
Compare ==
    /\ pc = "Compare"
    /\ n > 0               \* (if n = 0 the algorithm is already done)
    /\ LET a == CharAt(i + k)
          b == CharAt(j + k)
       IN
          IF a = b
             THEN /\ k' = k + 1
                  /\ IF k' = n
                        THEN /\ pc' = "Done"
                             /\ best' = IF i <= j THEN i ELSE j
                             /\ UNCHANGED <<s, n, f, i, j>>
                        ELSE /\ pc' = "Compare"
                             /\ UNCHANGED <<s, n, f, i, j, best>>
          ELSE IF a > b
                  THEN /\ i' = i + k + 1
                       /\ IF i' = j THEN i' = i' + 1
                       /\ k' = 0
                       /\ pc' = "Compare"
                       /\ UNCHANGED <<s, n, f, j, best>>
                  ELSE /\ j' = j + k + 1
                       /\ IF j' = i THEN j' = j' + 1
                       /\ k' = 0
                       /\ pc' = "Compare"
                       /\ UNCHANGED <<s, n, f, i, best>>

\* Stuttering step once the algorithm has terminated
Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<s, n, f, i, j, k, best, pc>>

Next ==
    \/ Check
    \/ Compare
    \/ Stutter

\* The complete specification
Spec ==
    Init /\ [][Next]_<<s, n, f, i, j, k, best, pc>>

\* Declare the identifiers required by the .cfg file
ASSUME
    /\ Spec
    /\ TypeInvariant
    /\ Correctness

====