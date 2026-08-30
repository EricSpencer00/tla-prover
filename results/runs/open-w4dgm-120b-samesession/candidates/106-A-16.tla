---- MODULE Util ----
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS MaxN

\* Set intersection test: returns TRUE iff the two sets share at least one element.
SetOverlap(A, B) == \E x \in A : x \in B

\* Set reduction: fold a commutative/associative reduction function over a set.
SetReduce(red, S, b) ==
    LET RECUR(s) ==
        IF s = {} THEN b
        ELSE LET x == CHOOSE y \in s : TRUE
             IN red(x, RECUR(s \ {x}))
    IN RECUR(S)

\* Sequence reduction: fold a reduction function over a sequence from the front.
SeqReduce(red, f, b) ==
    LET RECUR(i) ==
        IF i > Len(f) THEN b
        ELSE red(f[i], RECUR(i + 1))
    IN RECUR(1)

\* Index of an element in a sequence; -1 if not present.
SeqIndex(f, x) ==
    LET RECUR(i) ==
        IF i > Len(f) THEN -1
        ELSE IF f[i] = x THEN i
        ELSE RECUR(i + 1)
    IN RECUR(1)

\* Convert a sequence to the set of its elements.
SeqToSet(f) ==
    { f[i] : i \in 1..Len(f) }

SeqLast(f) == IF f = <<>> THEN -1 ELSE f[Len(f)]

SeqEmpty(f) == Len(f) = 0

\* Remove all occurrences of x from a sequence.
SeqRemove(f, x) ==
    IF f = <<>> THEN <<>>
    ELSE IF Head(f) = x THEN SeqRemove(Tail(f), x)
    ELSE <<Head(f)>> \o SeqRemove(Tail(f), x)

\* Intersection of a set of sets.
SetOfSetsIntersection(M) ==
    LET RECUR(S) ==
        IF S = {} THEN {}
        ELSE LET x == CHOOSE y \in S : TRUE
                 rest == RECUR(S \ {x})
             IN IF rest = {} THEN x ELSE rest \cap x
    IN RECUR(M)

\* Generate all permutation sequences of a finite set.
PermutationSequences(S) ==
    IF S = {} THEN { <<>> }
    ELSE UNION { [ x ] \o p : x \in S, p \in PermutationSequences(S \ {x}) }

\* Test helper: prints diagnostic when a boolean assertion fails.
Assertion(b) == IF b THEN TRUE ELSE TLC.Print("Assertion failed")

Spec == TRUE
Init == TRUE
Next == TRUE
Vars == {}
TypeOK == FALSE
StateConstraint == FALSE
SpecConstr == FALSE

====