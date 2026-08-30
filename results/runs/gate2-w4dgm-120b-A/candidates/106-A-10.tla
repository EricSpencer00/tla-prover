---- MODULE Util ----
EXTENDS FiniteSets, Sequences

CONSTANTS

SPECIFICATION == Spec
INIT == Init
NEXT == Next
INVARIANTS == Invariants
PROPERTIES == Properties

\* Whether two sets have any element in common.
Intersection(a, b) == \E x \in a : x \in b

\* Max and min elements of a non-empty set, defined by quantifier reduction.
SetMax(S) == CHOOSE x \in S :
                \A y \in S : y <= x
SetMin(S) == CHOOSE x \in S :
                \A y \in S : y >= x

\* Generalized set reduction (fold) with an accumulator.
SetReduce(S, op, init) ==
    LET f[T \in SUBSET S] ==
        IF T = {} THEN init
        ELSE LET x == CHOOSE y \in T : TRUE
                 rest == f[T \ {x}]
             IN op[x, rest]
    IN f[S]

\* Sequence reduction, folding from the left (library foldl).
SeqReduce(seq, op, init) == FoldL(seq, op, init)

\* Index of the first occurrence of x in seq, or 0 if absent (1-indexed).
SeqIndex(seq, x) ==
    LET g[i \in 1..Len(seq)] ==
        IF seq[i] = x THEN i ELSE IF i = Len(seq) THEN 0 ELSE g[i + 1]
    IN g[1]

\* Convert a sequence into the set of its elements.
SeqSet(seq) == {seq[i] : i \in 1..Len(seq)}

\* Last element of a sequence.
SeqLast(seq) == seq[Len(seq)]

\* Empty sequence predicate.
SeqEmpty(seq) == Len(seq) = 0

\* Remove all occurrences of x from seq.
SeqRemove(seq, x) ==
    SelectSeq(seq, LAMBDA e : e # x)

\* Intersection of a non-empty set of sets.
SetOfSetsIntersection(S) ==
    /\ S # {}
    /\ \E a \in S :
         /\ \A b \in S : b \subseteq a
         /\ a

\* All permutations of set s as sequences; requires s finite.
Permutations(s) ==
    IF s = {} THEN {<<>>}
    ELSE { <<x>> \o p : x \in s, p \in Permutations(s \ {x}) }

TestHelper(e) == e
====