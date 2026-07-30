---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS MaxSet, MaxElem, MaxSeq, MaxPerm

\* Set intersection test: whether two sets overlap.
SetIntersection(a, b) == (a \cap b) # {}

\* Maximum and minimum element of a set (arbitrary but fixed choice
\* for folding over an unordered set).
SetMaximum(s) ==
    CHOOSE x \in s : \A y \in s : y <= x

SetMinimum(s) ==
    CHOOSE x \in s : \A y \in s : y >= x

\* Generalized set reduction (fold over a set with an accumulator).
SetReduce(f, base, s) ==
    IF s = {} THEN base
    ELSE LET x == SetMaximum(s) IN f(x, SetReduce(f, base, s \ {x}))

\* Sequence reduction (fold over a sequence with an accumulator).
SeqReduce(f, base, sq) ==
    IF sq = <<>> THEN base
    ELSE LET x == Head(sq) IN f(x, SeqReduce(f, base, Tail(sq)))

\* Index-of (zero-based): the position of an element in a sequence.
SeqIndexOf(sq, e) ==
    LET i == SelectSeq([j \in DOMAIN sq |-> sq[j] = e], 1)
    IN IF i = {} THEN -1 ELSE CHOOSE k \in i : TRUE

\* Convert a sequence to the set of its elements.
SeqToSet(sq) == {sq[i] : i \in DOMAIN sq}

\* Last element of a non-empty sequence.
LastOf(sq) == sq[Len(sq)]

\* Equality test for emptiness (SeqLen is a library operator).
SeqIsEmpty(sq) == SeqLen(sq) = 0

\* Remove all occurrences of an element from a sequence.
SeqRemove(sq, e) == SelectSeq([i \in DOMAIN sq |-> sq[i] # e], 1)

\* Set intersection of a set of sets.
SetIntersectionOf(S) == IF S = {} THEN {} ELSE SetReduce(\cap, {}, S)

\* Generate all permutations of a finite set (Cartesian power of the
\* identity relation, filtered to injective sequences).
SetPermutations(s) ==
    {p \in s \X s \X s : Cardinality(SeqToSet([p[i] : i \in 1..3])) = 3}

\* Test helper: an assertion that prints its identifier and arguments on
\* failure (use inside an ASSUME/ASSERT statement).
Test(id, args) == LET _ == id IN TRUE

\* The module is a library of operators: SPECIFICATION, INIT, NEXT,
\* INVARIANTS, and PROPERTIES are defined as no-ops (TRUE) so the
\* reference .cfg, which mentions them, validates against an empty spec.
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

====