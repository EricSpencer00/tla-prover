---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\*------------------------------
\* Utility Operators
\*------------------------------

\* 1. Set intersection test (whether two sets overlap)
SetOverlap(S, T) == 
    /\ S # {}
    /\ T # {}
    /\ \E x \in S : x \in T

\* 2. Maximum element selection from a set
SetMax(S) == 
    IF S = {} THEN NULL 
    ELSE CHOOSE x \in S : \A y \in S : y <= x

\* 3. Minimum element selection from a set
SetMin(S) == 
    IF S = {} THEN NULL 
    ELSE CHOOSE x \in S : \A y \in S : y >= x

\* 4. Generalized set reduction (fold over a set with an accumulator)
RECURSIVE SetFold(_, _, _)
SetFold(S, init, op) ==
    IF S = {} THEN init
    ELSE 
        LET e == CHOOSE x \in S : TRUE
        IN op(SetFold(S \ {e}, init, op), e)

\* 5. Sequence reduction (fold over a sequence with an accumulator)
RECURSIVE SeqFold(_, _, _)
SeqFold(seq, init, op) ==
    IF Len(seq) = 0 THEN init
    ELSE op(SeqFold(Tail(seq), init, op), Head(seq))

\* 6. Finding the index of an element in a sequence (1‑based, 0 if not found)
RECURSIVE SeqIndex(_, _, _)
SeqIndex(seq, e, start) ==
    IF Len(seq) = 0 THEN 0
    ELSE IF Head(seq) = e THEN start
    ELSE SeqIndex(Tail(seq), e, start + 1)

SeqIndex(seq, e) == SeqIndex(seq, e, 1)

\* 7. Converting a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* 8. Getting the last element of a sequence
SeqLast(seq) == 
    IF Len(seq) = 0 THEN NULL 
    ELSE seq[Len(seq)]

\* 9. Testing if a sequence is empty
SeqIsEmpty(seq) == Len(seq) = 0

\* 10. Removing all occurrences of an element from a sequence
RECURSIVE SeqRemoveAll(_, _)
SeqRemoveAll(seq, e) ==
    IF Len(seq) = 0 THEN <<>>
    ELSE IF Head(seq) = e 
         THEN SeqRemoveAll(Tail(seq), e)
         ELSE <<Head(seq)>> \o SeqRemoveAll(Tail(seq), e)

\* 11. Computing the intersection of a set of sets
SetOfSetsIntersection(SS) ==
    IF SS = {} THEN {}
    ELSE INTERSECTION(SS)

\* 12. Generating all permutation sequences of a finite set
RECURSIVE Permutations(_)
Permutations(S) ==
    IF S = {} THEN { <<>> }
    ELSE UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

\* 13. Test helper for writing assertions that print diagnostic information on failure
TestHelper(expr, msg) == Assert(expr, msg)

\*------------------------------
\* Specification Skeleton (required identifiers)
\*------------------------------

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

====