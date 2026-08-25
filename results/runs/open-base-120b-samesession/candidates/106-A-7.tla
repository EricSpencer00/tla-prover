---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* 1. Set intersection test (whether two sets overlap)
Overlap(S, T) == \E x \in S : x \in T

\* 2. Maximum and minimum element selection from a set (assumes elements are comparable)
Max(S) ==
    IF S = {} THEN
        NULL
    ELSE
        LET m == CHOOSE x \in S : \A y \in S : y <= x
        IN m

Min(S) ==
    IF S = {} THEN
        NULL
    ELSE
        LET m == CHOOSE x \in S : \A y \in S : x <= y
        IN m

\* 3. Generalized set reduction (fold over a set with an accumulator)
RECURSIVE SetFold(_,_ ,_)
SetFold(S, a, Op) ==
    IF S = {} THEN
        a
    ELSE
        LET x == CHOOSE y \in S : TRUE
        IN SetFold(S \ {x}, Op(a, x), Op)

\* 4. Sequence reduction (fold over a sequence with an accumulator)
SeqFold(seq, a, Op) == FoldSeq(seq, a, Op)

\* 5. Finding the index of an element in a sequence (1‑based, 0 if absent)
IndexOf(seq, e) ==
    LET positions == { i \in 1..Len(seq) : seq[i] = e } IN
        IF positions = {} THEN 0 ELSE Min(positions)

\* 6. Converting a sequence to the set of its elements
SeqSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* 7. Getting the last element of a sequence
Last(seq) ==
    IF Len(seq) = 0 THEN
        NULL
    ELSE
        seq[Len(seq)]

\* 8. Testing if a sequence is empty
IsEmpty(seq) == Len(seq) = 0

\* 9. Removing all occurrences of an element from a sequence
RECURSIVE RemoveAll(_, _)
RemoveAll(seq, e) ==
    IF Len(seq) = 0 THEN
        <<>>
    ELSE IF seq[1] = e THEN
        RemoveAll(Tail(seq), e)
    ELSE
        <<seq[1]>> \o RemoveAll(Tail(seq), e)

\* 10. Computing the intersection of a set of sets
SetIntersection(SS) ==
    IF SS = {} THEN
        {}
    ELSE
        \cap SS

\* 11. Generating all permutation sequences of a finite set
RECURSIVE Permutations(_)
Permutations(S) ==
    IF S = {} THEN
        { <<>> }
    ELSE
        UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

\* 12. Test helper for writing assertions that print diagnostic information on failure
AssertHelper(cond, msg) ==
    IF cond THEN
        TRUE
    ELSE
        Print(msg) /\ FALSE

====