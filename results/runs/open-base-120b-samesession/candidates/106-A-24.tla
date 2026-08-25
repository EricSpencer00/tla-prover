---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\*=====================================================================
\* Utility operators
\*=====================================================================

\* 1. Set overlap test (whether two sets intersect)
SetOverlap(A, B) == \E x \in A : x \in B

\* 2. Maximum and minimum element selection from a (non‑empty) set
SetMax(S) == 
    IF S = {} THEN NULL
    ELSE CHOOSE x \in S : \A y \in S : y <= x

SetMin(S) == 
    IF S = {} THEN NULL
    ELSE CHOOSE x \in S : \A y \in S : x <= y

\* 3. Generalized set reduction (fold over a set with an accumulator)
SetFold(F, acc, S) == SeqFold(F, acc, ToSeq(S))

\* 4. Sequence reduction (fold over a sequence with an accumulator)
SeqFold(F, acc, seq) ==
    IF Len(seq) = 0
    THEN acc
    ELSE SeqFold(F, F(acc, Head(seq)), Tail(seq))

\* 5. Index of an element in a sequence (1‑based, 0 if not present)
SeqIndex(seq, elem) ==
    IF Len(seq) = 0
    THEN 0
    ELSE IF Head(seq) = elem
         THEN 1
         ELSE LET i == SeqIndex(Tail(seq), elem) IN
                IF i = 0 THEN 0 ELSE i + 1

\* 6. Convert a sequence to the set of its elements
SeqToSet(seq) == Set(seq)

\* 7. Last element of a sequence (NULL if the sequence is empty)
SeqLast(seq) ==
    IF Len(seq) = 0
    THEN NULL
    ELSE seq[Len(seq)]

\* 8. Test whether a sequence is empty
SeqEmpty(seq) == Len(seq) = 0

\* 9. Remove all occurrences of an element from a sequence
SeqRemoveAll(seq, elem) ==
    IF Len(seq) = 0
    THEN <<>>
    ELSE IF Head(seq) = elem
         THEN SeqRemoveAll(Tail(seq), elem)
         ELSE <<Head(seq)>> \o SeqRemoveAll(Tail(seq), elem)

\* 10. Intersection of a set of sets
SetIntersectionOfSetOfSets(SS) ==
    IF SS = {}
    THEN {}
    ELSE LET S == CHOOSE s \in SS : TRUE
             Rest == SS \ {S}
         IN IF Rest = {}
            THEN S
            ELSE S \cap SetIntersectionOfSetOfSets(Rest)

\* 11. Generate all permutations of a finite set
Permutations(S) ==
    IF S = {}
    THEN {<<>>}
    ELSE UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

\* 12. Test helper for assertions with diagnostic messages
TestHelper(cond, msg) == Assert(cond, msg)

\*=====================================================================
\* Trivial specification (required identifiers)
\*=====================================================================

VARIABLES

Init == TRUE

Next == UNCHANGED <<>>

Spec == Init /\ [][Next]_<<>>

INVARIANTS == TRUE

PROPERTIES == TRUE

=============================================================================