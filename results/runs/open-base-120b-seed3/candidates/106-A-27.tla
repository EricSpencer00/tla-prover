---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\* Utility operators
\* ----------------------------------------------------------------------

\* 1. Set intersection test (whether two sets overlap)
SetOverlap(S, T) == \E x \in S : x \in T

\* 2. Maximum element of a (numeric) set
SetMax(S) == 
    IF S = {} THEN NULL 
    ELSE CHOOSE x \in S : \A y \in S : y <= x

\* 2b. Minimum element of a (numeric) set
SetMin(S) == 
    IF S = {} THEN NULL 
    ELSE CHOOSE x \in S : \A y \in S : x <= y

\* 3. Generalized set reduction (fold over a set with an accumulator)
SetReduce(S, op, acc) ==
    IF S = {} THEN acc
    ELSE 
        LET e == CHOOSE x \in S IN
            SetReduce(S \ {e}, op, op[acc, e])

\* 4. Sequence reduction (fold over a sequence with an accumulator)
SeqReduce(seq, op, acc) == FoldSeq(seq, op, acc)

\* 5. Finding the index of an element in a sequence (returns 0 if not found)
IndexOf(seq, elem) ==
    IF elem \in SeqToSet(seq) THEN
        CHOOSE i \in 1..Len(seq) : seq[i] = elem
    ELSE 0

\* 6. Converting a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* 7. Getting the last element of a sequence
Last(seq) == seq[Len(seq)]

\* 8. Testing if a sequence is empty
IsEmpty(seq) == Len(seq) = 0

\* 9. Removing all occurrences of an element from a sequence
RemoveAll(seq, elem) ==
    IF Len(seq) = 0 THEN <<>>
    ELSE IF Head(seq) = elem THEN RemoveAll(Tail(seq), elem)
    ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), elem)

\* 10. Intersection of a set of sets
SetIntersection(SS) == { x \in UNION SS : \A s \in SS : x \in s }

\* 11. Generating all permutation sequences of a finite set
PermutationsOf(S) == Permutations(S)  \* Permutations is provided by FiniteSets

\* 12. Test helper for assertions that print diagnostic information on failure
TestHelper(msg, cond) ==
    IF cond THEN TRUE ELSE Print(msg) /\ FALSE

\* ----------------------------------------------------------------------
\* Trivial specification scaffolding (required identifiers)
\* ----------------------------------------------------------------------
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====