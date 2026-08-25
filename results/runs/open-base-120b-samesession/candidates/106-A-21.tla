---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* 1. Set intersection test (whether two sets overlap)
SetOverlap(S, T) == \E x \in S : x \in T

\* 2. Maximum and minimum element selection from a set
SetMax(S) == IF S = {} THEN NULL ELSE Max(S)
SetMin(S) == IF S = {} THEN NULL ELSE Min(S)

\* 3. Generalized set reduction (fold over a set with an accumulator)
SetReduce(S, op, init) ==
    IF S = {} THEN
        init
    ELSE
        LET e == CHOOSE x \in S IN
            SetReduce(S \ {e}, op, op(init, e))

\* 4. Sequence reduction (fold over a sequence with an accumulator)
SeqReduce(seq, op, init) ==
    IF Len(seq) = 0 THEN
        init
    ELSE
        SeqReduce(Tail(seq), op, op(Head(seq), init))

\* 5. Finding the index of an element in a sequence
IndexOf(seq, elem) ==
    IF \E i \in 1..Len(seq) : seq[i] = elem THEN
        MIN { i \in 1..Len(seq) : seq[i] = elem }
    ELSE
        0

\* 6. Converting a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* 7. Getting the last element of a sequence
Last(seq) == IF Len(seq) = 0 THEN NULL ELSE seq[Len(seq)]

\* 8. Testing if a sequence is empty
IsEmpty(seq) == Len(seq) = 0

\* 9. Removing all occurrences of an element from a sequence
RemoveAll(seq, elem) ==
    IF Len(seq) = 0 THEN
        <<>>
    ELSE IF Head(seq) = elem THEN
        RemoveAll(Tail(seq), elem)
    ELSE
        <<Head(seq)>> \o RemoveAll(Tail(seq), elem)

\* 10. Computing the intersection of a set of sets
SetIntersection(Sets) ==
    IF Sets = {} THEN {} ELSE INTERSECTION Sets

\* 11. Generating all permutation sequences of a finite set
PermutationsOfSet(S) == Permutations(S)

\* 12. Test helper for writing assertions that print diagnostic information on failure
TestHelper(expr, msg) == Assert(expr, msg)

====