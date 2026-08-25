---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\* Utility operators
\* ----------------------------------------------------------------------

\* 1. Set intersection test (whether two sets overlap)
SetOverlap(S, T) == (S \cap T) # {}

\* 2. Maximum element selection from a set (assumes elements are comparable)
SetMax(S) ==
    CHOOSE x \in S :
        \A y \in S : y <= x

\* 2b. Minimum element selection from a set
SetMin(S) ==
    CHOOSE x \in S :
        \A y \in S : x <= y

\* 3. Generalized set reduction (fold over a set with an accumulator)
\*    f is a binary operator, a is the initial accumulator value
SetFold(S, f(_,_), a) ==
    IF S = {} THEN a
    ELSE
        LET x == CHOOSE y \in S IN
            SetFold(S \ {x}, f, f(x, a))

\* 4. Sequence reduction (fold over a sequence with an accumulator)
SeqFold(seq, f(_,_), a) ==
    IF Len(seq) = 0 THEN a
    ELSE SeqFold(Tail(seq), f, f(Head(seq), a))

\* 5. Finding the index of an element in a sequence (1‑based, 0 if absent)
SeqIndex(seq, e) ==
    IF Len(seq) = 0 THEN 0
    ELSE IF Head(seq) = e THEN 1
    ELSE
        LET i == SeqIndex(Tail(seq), e) IN
            IF i = 0 THEN 0 ELSE i + 1

\* 6. Converting a sequence to the set of its elements
SeqToSet(seq) ==
    { seq[i] : i \in 1..Len(seq) }

\* 7. Getting the last element of a sequence (returns {} if empty)
SeqLast(seq) ==
    IF Len(seq) = 0 THEN {} ELSE seq[Len(seq)]

\* 8. Testing if a sequence is empty
SeqIsEmpty(seq) == Len(seq) = 0

\* 9. Removing all occurrences of an element from a sequence
SeqRemoveAll(seq, e) ==
    IF Len(seq) = 0 THEN <<>>
    ELSE IF Head(seq) = e THEN SeqRemoveAll(Tail(seq), e)
    ELSE <<Head(seq)>> \o SeqRemoveAll(Tail(seq), e)

\* 10. Computing the intersection of a set of sets
SetIntersection(SS) ==
    IF SS = {} THEN {}
    ELSE
        LET X == CHOOSE Y \in SS IN
            IF SS \ {X} = {} THEN X
            ELSE SetIntersection(SS \ {X}) \cap X

\* 11. Generating all permutation sequences of a finite set
SetPermutations(S) ==
    IF S = {} THEN { <<>> }
    ELSE
        UNION { <<x>> \o p : x \in S, p \in SetPermutations(S \ {x}) }

\* 12. Test helper for writing assertions that print diagnostic information on failure
AssertHelper(cond, msg) ==
    IF cond THEN TRUE
    ELSE Print(msg) /\ FALSE

====