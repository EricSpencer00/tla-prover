---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* 1. Set intersection test (whether two sets overlap)
SetOverlap(S, T) == \E x \in S : x \in T

\* 2. Maximum element of a set (NULL if the set is empty)
SetMax(S) == IF S = {} THEN NULL ELSE CHOOSE x \in S : \A y \in S : y <= x

\* 3. Minimum element of a set (NULL if the set is empty)
SetMin(S) == IF S = {} THEN NULL ELSE CHOOSE x \in S : \A y \in S : x <= y

\* 4. Generalized set reduction (fold over a set with an accumulator)
SetFold(S, init, f) ==
    IF S = {} THEN init
    ELSE
        LET x == CHOOSE y \in S : TRUE
        IN SetFold(S \ {x}, f(init, x), f)

\* 5. Sequence reduction (fold over a sequence with an accumulator)
SeqFold(seq, init, f) == FoldSeq(seq, init, f)

\* 6. Finding the index of an element in a sequence (first occurrence, NULL if absent)
IndexOf(seq, elem) ==
    IF \E i \in 1..Len(seq) : seq[i] = elem
    THEN SetMin({ i \in 1..Len(seq) : seq[i] = elem })
    ELSE NULL

\* 7. Converting a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* 8. Getting the last element of a sequence (NULL if empty)
SeqLast(seq) == IF Len(seq) = 0 THEN NULL ELSE seq[Len(seq)]

\* 9. Testing if a sequence is empty
SeqIsEmpty(seq) == Len(seq) = 0

\* 10. Removing all occurrences of an element from a sequence
RemoveAll(seq, elem) ==
    IF Len(seq) = 0 THEN <<>>
    ELSE IF Head(seq) = elem THEN RemoveAll(Tail(seq), elem)
    ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), elem)

\* 11. Computing the intersection of a set of sets
SetIntersectionAll(S) == IF S = {} THEN {} ELSE \bigcap S

\* 12. Generating all permutation sequences of a finite set
Permutations(S) ==
    IF S = {} THEN { <<>> }
    ELSE UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

\* 13. Test helper for writing assertions that print diagnostic information on failure
TestHelper(cond, msg) ==
    IF cond THEN TRUE ELSE (Print(msg) /\ FALSE)

====