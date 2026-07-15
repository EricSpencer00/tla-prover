---- MODULE LeastCircularSubstring ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS CharacterSet, Nat

\* Sentinel value for "undefined" entries in the failure function.
\* Must be outside the range 0..2*maxLen so it never collides with a valid index.
Sentinel == 2 * Nat

VARIABLES
    str,          \* input string, a sequence over CharacterSet
    n,            \* length of str
    Failure,      \* array (function) from 0..2*n-1 to Nat ∪ {Sentinel}
    j,            \* pattern‑match index (the "k" in Booth's algorithm)
    i,            \* outer loop counter, runs from 1 to 2*n-1
    best,         \* current best rotation offset, 0..n-1
    pc            \* program counter, one of the labeled steps

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Idx(p) == p % n          \* circular index into str
CharAt(p) == str[Idx(p) + 1]   \* sequences are 1‑indexed in TLA+, so add 1

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ str \in [1..n -> CharacterSet]          \* will be constrained below
    /\ n \in Nat
    /\ Len(str) = n
    /\ Failure = [p \in 0..(2*n - 1) |-> Sentinel]
    /\ j = Sentinel
    /\ i = 1
    /\ best = 0
    /\ pc = "OuterLoop"

\* ----------------------------------------------------------------------
\* Actions corresponding to the labeled steps
\* ----------------------------------------------------------------------
OuterLoop ==
    /\ pc = "OuterLoop"
    /\ i < 2 * n
    /\ pc' = "FailureLookup"
    /\ UNCHANGED << str, n, Failure, j, i, best >>

FailureLookup ==
    /\ pc = "FailureLookup"
    /\ j = Failure[i - 1]          \* lookup for position i-1 (since i starts at 1)
    /\ pc' = "InnerCompare"
    /\ UNCHANGED << str, n, Failure, i, best >>

InnerCompare ==
    /\ pc = "InnerCompare"
    /\ LET cur  == CharAt(i)
           cand == CharAt(best + i - j) IN
       IF cur = cand
          THEN /\ i' = i + 1
                /\ pc' = "OuterLoop"
                /\ UNCHANGED << str, n, Failure, j, best >>
          ELSE
             IF j # Sentinel
                THEN /\ IF cur < cand THEN best' = i ELSE best' = best
                     /\ j' = Failure[j]
                     /\ pc' = "InnerCompare"
                     /\ UNCHANGED << str, n, Failure, i >>
                ELSE /\ IF cur < cand THEN best' = i ELSE best' = best
                     /\ Failure' = [Failure EXCEPT ![i - 1] = IF cur = cand
                                                                    THEN Sentinel
                                                                    ELSE j + 1]
                     /\ j' = Failure[i - 1]
                     /\ pc' = "OuterLoop"
                     /\ i' = i + 1
                     /\ UNCHANGED << str, n, best >>

Terminate ==
    /\ pc = "OuterLoop"
    /\ i >= 2 * n
    /\ pc' = "Done"
    /\ UNCHANGED << str, n, Failure, j, i, best >>

Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED << str, n, Failure, j, i, best, pc >>

Next ==
    \/ OuterLoop
    \/ FailureLookup
    \/ InnerCompare
    \/ Terminate
    \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<str, n, Failure, j, i, best, pc>>

\* ----------------------------------------------------------------------
\* Safety invariant: type correctness
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ str \in [1..n -> CharacterSet]
    /\ n \in Nat
    /\ Failure \in [0..(2*n - 1) -> (Nat \cup {Sentinel})]
    /\ j \in Nat \cup {Sentinel}
    /\ i \in Nat
    /\ best \in 0..(n - 1)
    /\ pc \in {"OuterLoop", "FailureLookup", "InnerCompare", "Done"}

\* ----------------------------------------------------------------------
\* Correctness invariant: best is the lexicographically least rotation
\* ----------------------------------------------------------------------
Correctness ==
    /\ best \in 0..(n - 1)
    /\ \A k \in 1..n :
          LexLeq(best, k)

\* Lexicographic less‑or‑equal comparison of two rotations.
LexLeq(p, q) ==
    \A r \in 0..(n - 1) :
        LET a == CharAt(p + r)
            b == CharAt(q + r) IN
        a < b \/ a = b

\* ----------------------------------------------------------------------
\* The set of invariants required by the .cfg file
\* ----------------------------------------------------------------------
TypeInvariant == TypeInvariant
Correctness   == Correctness

=============================================================================