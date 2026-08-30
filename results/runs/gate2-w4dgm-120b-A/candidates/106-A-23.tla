---- MODULE Util ----
EXTENDS Sequences, FiniteSets

CONSTANTS NONE

\* Utility operators for sequence and set manipulation, used by the kv-store
\* specifications. All are pure functions; there is no system state here.

\* 1) Set intersection test (whether two sets overlap).
Intersecting(a, b) == \E x \in a : x \in b

\* 2) Maximum and minimum element selected from a set.
Maximum(s) == CHOOSE x \in s : \A y \in s : y <= x
Minimum(s) == CHOOSE x \in s : \A y \in s : y >= x

\* 3) Generalized set reduction (fold over a set with an accumulator).
RECURSIVE SetReduce(_, _)
SetReduce(f, S) == IF S = {} THEN NONE
                   ELSE LET x == CHOOSE y \in S : TRUE
                            r == SetReduce(f, S \ {x})
                        IN IF r = NONE THEN f[x] ELSE f[r, x]

\* 4) Sequence reduction (fold over a sequence with an accumulator, using
\*    a library fold operator).
SequenceReduce(f, seq) == IF seq = << >> THEN NONE
                          ELSE LET x == Head(seq)
                                   r == SequenceReduce(f, Tail(seq))
                               IN IF r = NONE THEN f[x] ELSE f[r, x]

\* 5) Find the index of an element in a sequence (1-based, NONE if not found).
FindIndex(seq, e) == CHOOSE k \in 1..Len(seq) : seq[k] = e

\* 6) Convert a sequence to the set of its elements.
SeqToSet(seq) == { seq[k] : k \in 1..Len(seq) }

\* 7) Get the last element of a sequence.
Last(seq) == seq[Len(seq)]

\* 8) Test if a sequence is empty.
IsEmpty(seq) == seq = << >>

\* 9) Remove all occurrences of an element from a sequence.
RemoveAll(seq, e) == SELECT seq[k] : seq[k] # e

\* 10) Intersection of a set of sets.
SetIntersection(T) == { x \in UNION T : \A t \in T : x \in t }

\* 11) Generate all permutation sequences of a finite set.
PermutationsOf(S) == { p \in [1..Cardinality(S) -> S] :
    \A i, j \in 1..Cardinality(S) : (p[i] = p[j]) => i = j }

\* 12) Test helper: prints diagnostic info on failure.
Assert(pred, msg) == IF pred THEN "ok" ELSE
    (Print(msg); "failed")
====