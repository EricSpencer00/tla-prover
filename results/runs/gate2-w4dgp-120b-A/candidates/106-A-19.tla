---- MODULE Util ----
\* Utility library module for the key-value store specifications. Provides reusable
\* operators for set and sequence manipulation, such as set intersection tests,
\* set and sequence reduction, element indexing, permutation generation, and a
\* diagnostic test helper. This module has no actors or state of its own; it is
\* imported by other modules that need these operators.
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS

ASSUME TRUE

\* Set intersection test: returns TRUE iff two sets share at least one element.
INTERSECT(A, B) == \E a \in A : a \in B

\* Maximum element of a set.
Max(S) == CHOOSE m \in S : \A x \in S : x <= m

\* Minimum element of a set.
Min(S) == CHOOSE m \in S : \A x \in S : m <= x

\* Generalized set reduction: fold a binary operator over a set with an
\* accumulator. Order is nondeterministic, so this works only for commutative ops
\* like set union or numeric sum.
SetReduce(f, seed, S) == LET
    reducer(s, acc) ==
        IF s = {} THEN acc
        ELSE LET x == CHOOSE e \in s : TRUE IN f(x, reducer(s \ {x}, acc))
    IN reducer(S, seed)

\* Sequence reduction (fold) using the library's FoldSeq operator with a left
\* accumulator.
SeqReduce(f, seed, seq) == FoldSeq(f, seed, seq)

\* Find the index of element x in sequence seq; returns 0 if x is not present.
IndexOf(seq, x) == LET
    finder(i) == IF i > Len(seq) THEN 0
                 ELSE IF seq[i] = x THEN i ELSE finder(i + 1)
    IN finder(1)

\* Convert a sequence to the set of its elements (duplicate elements of the
\* sequence contribute once to the set).
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* Get the last element of a sequence; 0 if the sequence is empty.
Last(seq) == IF seq = << >> THEN 0 ELSE seq[Len(seq)]

\* True iff the sequence seq is empty.
Empty(seq) == Len(seq) = 0

\* Remove all occurrences of element x from sequence seq.
RemoveAll(seq, x) == SelectSeq(seq, LAMBDA y : y # x)

\* Intersection of a set of sets: the elements common to every member set.
SetIntersection(S) ==
    IF S = {} THEN {}
    ELSE LET
        inter(s, acc) == IF s = {} THEN acc ELSE inter(s \ {CHOOSE e \in s : TRUE}, acc \cap CHOOSE e \in s : TRUE)
        in inter(S, CHOOSE x \in S : TRUE)

\* Generate all permutation sequences of a finite set of elements.
Permutations(S) ==
    IF S = {} THEN { << >> }
    ELSE LET
        perms(s) ==
            IF s = {} THEN { << >> }
            ELSE UNION { [x] \o p : x \in s, p \in perms(s \ {x}) }
        IN perms(S)

\* Test helper that prints diagnostic information on failure. Returns TRUE so it
\* can be placed in an ASSUME or a CONSTRAINT without affecting semantics.
TestHelper(expr) == expr

SPECIFICATION Spec

Spec == TRUE

INIT Init == TRUE

NEXT Next == TRUE

INVARIANTS

CONSTRAINTS

PROPERTIES

====