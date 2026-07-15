---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Constants required by the .cfg file
\* ----------------------------------------------------------------------
CONSTANTS
    CharacterSet, \* a finite subset of Nat supplied by the .cfg
    Nat          \* the usual natural numbers (provided by Naturals)

\* ----------------------------------------------------------------------
\* Sentinel value for undefined entries in the failure function
\* ----------------------------------------------------------------------
Sentinel == -1

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    s,          \* input string, a sequence of characters (zero-indexed)
    n,          \* length of s
    F,          \* failure function, a function from 0..2*n to Nat \cup {Sentinel}
    i,          \* pattern‑match index (current failure function lookup)
    k,          \* outer loop counter, runs from 1 to 2*n
    best,       \* best rotation offset found so far, in 0..n-1
    pc          \* program counter, one of the labeled steps

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Idx(j) == j % n                \* circular index into s

CharAt(j) == s[Idx(j)]         \* character at position j modulo n

\* ----------------------------------------------------------------------
\* Initial state (corresponds to the description's "initial state")
\* ----------------------------------------------------------------------
Init ==
    /\ s \in [0..] -> CharacterSet
    /\ n = Len(s)
    /\ n >= 0
    /\ F = [j \in 0..2*n |-> Sentinel]
    /\ i = Sentinel
    /\ k = 1
    /\ best = 0
    /\ pc = "OuterCheck"

\* ----------------------------------------------------------------------
\* Action definitions for each labeled step of the algorithm
\* ----------------------------------------------------------------------
OuterCheck ==
    /\ pc = "OuterCheck"
    /\ IF k < 2 * n + 1
          THEN /\ pc' = "FailureLookup"
               /\ UNCHANGED <<s, n, F, i, k, best>>
          ELSE /\ pc' = "Terminated"
               /\ UNCHANGED <<s, n, F, i, k, best, best>>
    /\ k' = k
    /\ i' = i
    /\ best' = best
    /\ F' = F

FailureLookup ==
    /\ pc = "FailureLookup"
    /\ i' = F[Idx(k + best)]
    /\ pc' = "InnerLoop"
    /\ UNCHANGED <<s, n, F, k, best>>

InnerLoop ==
    /\ pc = "InnerLoop"
    /\ IF i # Sentinel /\ s[Idx(k + best)] = s[Idx(k + best + i + 1)]
          THEN /\ i' = i - 1
               /\ pc' = "InnerLoop"
               /\ UNCHANGED <<s, n, F, k, best>>
          ELSE /\ pc' = "PostCompare"
               /\ UNCHANGED <<i, s, n, F, k, best>>

PostCompare ==
    /\ pc = "PostCompare"
    /\ LET cur == s[Idx(k + best)]
          cand == s[Idx(k + best + i + 1)]
       IN
       /\ IF cur # cand /\ i = Sentinel /\ cur < cand
             THEN /\ best' = Idx(k + best)
                  /\ F' = [F EXCEPT ![Idx(k + best)] = 0]
             ELSE IF cur # cand /\ i = Sentinel /\ cur > cand
                     THEN /\ best' = best
                          /\ F' = [F EXCEPT ![Idx(k + best)] = 0]
                     ELSE /\ best' = best
                          /\ IF cur = cand
                               THEN /\ F' = [F EXCEPT ![Idx(k + best)] = i + 1]
                               ELSE /\ F' = [F EXCEPT ![Idx(k + best)] = 0]
       /\ pc' = "Increment"
       /\ UNCHANGED <<s, n, i, k>>

Increment ==
    /\ pc = "Increment"
    /\ k' = k + 1
    /\ pc' = "OuterCheck"
    /\ UNCHANGED <<s, n, F, i, best>>

Terminated ==
    /\ pc = "Terminated"
    /\ UNCHANGED <<s, n, F, i, k, best, pc>>

Stutter ==
    /\ pc = "Terminated"
    /\ UNCHANGED <<s, n, F, i, k, best, pc>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ OuterCheck
    \/ FailureLookup
    \/ InnerLoop
    \/ PostCompare
    \/ Increment
    \/ Terminated
    \/ Stutter

\* ----------------------------------------------------------------------
\* Safety invariant (type correctness)
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ s \in [0..] -> CharacterSet
    /\ n = Len(s)
    /\ F \in [0..2*n -> (Nat \cup {Sentinel})]
    /\ i \in Nat \cup {Sentinel}
    /\ k \in 1..(2*n + 1)
    /\ best \in 0..(n - 1) \/ (n = 0)
    /\ pc \in {"OuterCheck", "FailureLookup", "InnerLoop",
               "PostCompare", "Increment", "Terminated"}

\* ----------------------------------------------------------------------
\* Correctness invariant (lexicographically minimal rotation)
\* ----------------------------------------------------------------------
\* Rotation of s by offset o (zero‑indexed) produces the sequence
\* s[o], s[o+1], …, s[n-1], s[0], …, s[o-1]
Rotation(o) ==
    [j \in 0..(n-1) |-> s[Idx(o + j)]]

Correctness ==
    /\ IF n = 0 THEN best = 0
       ELSE /\ best \in 0..(n-1)
            /\ \A o \in 0..(n-1) : Rotation(best) <=_lex Rotation(o)

\* Lexicographic ordering (non‑decreasing)
\* s <=_lex t iff there exists an index j where the prefixes are equal
\* and the character at j in s is less than that in t, or the strings are equal.
<=_lex(t, u) ==
    \A j \in 0..(n-1) :
        ( \A m \in 0..j-1 : t[m] = u[m] ) => t[j] <= u[j]

\* ----------------------------------------------------------------------
\* Full specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<s, n, F, i, k, best, pc>>

\* ----------------------------------------------------------------------
\* Theorem (optional, not required by the .cfg but useful for readers)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeInvariant

=============================================================================