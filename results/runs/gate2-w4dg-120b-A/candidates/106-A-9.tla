---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS MaxSize, MaxElement

\* A set intersection test: whether two sets overlap.
INTERSECTION(a, b) == Cardinality(a \cap b) > 0

\* Maximum element selection from a non-empty set.
MAXIMUM(S) ==
    LET m[x \in S] ==
        IF \A y \in S : y <= x THEN x
        ELSE m[CHOOSE y \in S : y > x]
    IN m[CHOOSE x \in S : \A y \in S : x >= y]

\* Minimum element selection from a non-empty set.
MINIMUM(S) ==
    LET m[x \in S] ==
        IF \A y \in S : y >= x THEN x
        ELSE m[CHOOSE y \in S : y < x]
    IN m[CHOOSE x \in S : \A y \in S : x <= y]

\* Generalized set reduction (fold over a set with an accumulator).
REDUCESET(f, a, S) ==
    IF S = {} THEN a
    ELSE LET x == CHOOSE y \in S : TRUE
         IN REDUCESET(f, f[a, x], S \ {x})

\* Sequence reduction (fold over a sequence with an accumulator), using the
\* library's FoldSeq operator (which has the same signature as a set fold).
REDUCESEQ(f, a, s) == FoldSeq(f, a, s)

\* Find the index of an element in a sequence (CHOOSE returns a natural index
\* into the sequence's domain, which starts at 1).
INDEX(s, x) == CHOOSE i \in DOMAIN s : s[i] = x

\* Convert a sequence to the set of its elements.
SEQTOSET(s) == {s[i] : i \in DOMAIN s}

\* The last element of a sequence.
LAST(s) == s[Len(s)]

\* Test whether a sequence is empty (its domain is empty, i.e. Len(s) = 0).
ISEMPTY(s) == Len(s) = 0

\* Remove all occurrences of an element from a sequence.
REMOVEALL(s, x) ==
    LET f[a \in Seq(S), y \in S] == IF y = x THEN a ELSE Append(a, y)
    IN REDUCESEQ(f, <<>>, s)

\* Intersection of a set of sets.
INTERSECTIONOF(S) == REDUCESET(\cap, Universe, S)

\* Generate all permutation sequences of a finite set.
PERMUTATIONS(S) ==
    IF S = {} THEN {<<>>}
    ELSE { Append(s, x) : x \in S, s \in PERMUTATIONS(S \ {x}) }

\* Test helper for writing assertions that print diagnostic information on
\* failure (the diagnostic is a value, not a string, so it can be shown).
ASSERT(e, d) == IF e THEN TRUE ELSE d

\* Stub operators that satisfy the .cfg's identifier set, though they do
\* nothing in this library module (the real spec defines them elsewhere).
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

====