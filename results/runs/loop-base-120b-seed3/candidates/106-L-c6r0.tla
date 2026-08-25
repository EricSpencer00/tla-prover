---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\*------------------------------ Utility Operators ------------------------------

\* 1. Set intersection test (whether two sets overlap)
SetOverlap(A, B) ==
    /\ A # {}
    /\ B # {}
    /\ \E x \in A : x \in B

\* 2. Maximum and minimum element selection from a set (assumes numeric elements)
SetMax(S) ==
    IF S = {} THEN NULL
    ELSE CHOOSE x \in S : \A y \in S : x >= y

SetMin(S) ==
    IF S = {} THEN NULL
    ELSE CHOOSE x \in S : \A y \in S : x <= y

\* 3. Generalized set reduction (fold over a set with an accumulator)
RECURSIVE SetReduce(_, _, _)
SetReduce(S, init, f) ==
    IF S = {} THEN init
    ELSE LET e == CHOOSE x \in S
         IN f(e, SetReduce(S \ {e}, init, f))

\* 4. Sequence reduction (fold over a sequence with an accumulator)
SeqReduce(seq, init, f) ==
    FoldSeq(seq, init, f)   \* defined in the Sequences module

\* 5. Finding the index of an element in a sequence (1-based index, NULL if absent)
SeqIndexOf(seq, elem) ==
    IF \E i \in DOMAIN seq : seq[i] = elem
    THEN CHOOSE i \in DOMAIN seq : seq[i] = elem
    ELSE NULL

\* 6. Converting a sequence to the set of its elements
SeqToSet(seq) ==
    { seq[i] : i \in DOMAIN seq }

\* 7. Getting the last element of a sequence (NULL if empty)
LastElem(seq) ==
    IF Len(seq) = 0 THEN NULL
    ELSE seq[Len(seq)]

\* 8. Testing if a sequence is empty
IsSeqEmpty(seq) ==
    Len(seq) = 0

\* 9. Removing all occurrences of an element from a sequence (preserves order)
SeqRemoveAll(seq, elem) ==
    Filter(seq, LAMBDA x : x # elem)

\* 10. Computing the intersection of a set of sets
SetIntersectionAll(SS) ==
    INTERSECTION SS

\* 11. Generating all permutation sequences of a finite set
RECURSIVE Permutations(_)
Permutations(S) ==
    IF S = {} THEN { << >> }
    ELSE UNION { << e >> \o p : e \in S, p \in Permutations(S \ {e}) }

\* 12. Test helper for writing assertions that print diagnostic information on failure
AssertHelper(cond, msg) ==
    IF cond
    THEN TRUE
    ELSE (Print(msg) /\ FALSE)

=============================================================================