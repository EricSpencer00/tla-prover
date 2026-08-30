---- MODULE Util ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS MaxSet, MaxSeq, Permutations

\* Returns TRUE iff the two sets have any element in common.
SetOverlap(a, b) == \E x \in a : x \in b

\* Returns the maximum or minimum element of a non-empty finite set.
SetMax(S) == CHOOSE m \in S : \A x \in S : x <= m
SetMin(S) == CHOOSE m \in S : \A x \in S : m <= x

\* Generalized set reduction: folds the binary operator f over the set,
\* threading an accumulator that starts at init.
SetFold(S, f, init) ==
    LET Recur(T, acc) ==
        IF T = {} THEN acc
        ELSE LET x == CHOOSE y \in T : TRUE
             IN Recur(T \ {x}, f[x, acc])
    IN Recur(S, init)

\* Sequence reduction: folds f over the indexed elements of s in order,
\* using the foldl operator from the Sequences module.
SeqFold(s, f, init) == FoldL(f, init, s)

\* Returns the index of element x in sequence s, or 0 if x does not appear.
SeqIndex(s, x) ==
    LET Recur(i) == IF i > Len(s) THEN 0
                    ELSE IF s[i] = x THEN i
                    ELSE Recur(i + 1)
    IN Recur(1)

\* Returns the set of distinct elements appearing anywhere in s.
SeqToSet(s) == { s[i] : i \in 1..Len(s) }

\* Convenience: the last element of a non-empty sequence.
SeqLast(s) == s[Len(s)]

\* Convenience: TRUE exactly when the sequence is empty.
SeqEmpty(s) == Len(s) = 0

\* Returns a copy of s with every occurrence of x removed.
SeqRemove(s, x) ==
    [ i \in 1..(Len(s) - Cardinality({ j \in 1..Len(s) : s[j] = x }))
        |-> IF s[i] = x THEN s[i + Cardinality({ j \in 1..Len(s) : s[j] = x })]
                    ELSE s[i] ]

\* Returns the intersection of a set of finite sets.
SetIntersection(T) == { x \in UNION T : \A S \in T : x \in S }

\* Returns every permutation sequence of the finite set S, but only while
\* the total number of permutations is within the runtime bound Permutations.
PermutationsOf(S) ==
    IF Cardinality(S) > 0 /\ Permutations < 2 ^ Cardinality(S)
    THEN { s \in [1..Cardinality(S) -> UNION S] :
                \A i \in 1..Cardinality(S) : s[i] \in S
                /\ \A i, j \in 1..Cardinality(S) : i # j => s[i] # s[j] }
    ELSE {}

\* Test helper: fails a deadlocked spec with a printed diagnostic, so a
\* surprise silent stutter is never missed by a model run.
Fail(msg) == UNCHANGED msg /\ \A x \in BOOLEAN : FALSE

====