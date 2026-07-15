---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\*  Utility operators
\* ----------------------------------------------------------------------

\* 1. Set intersection test: true iff two sets overlap (have a common element)
SetOverlap(A, B) == \E x \in A : x \in B

\* 2. Maximum and minimum element selection from a finite, non‑empty set
SetMax(S) == 
    IF S = {} THEN CHOOSE x : FALSE 
    ELSE 
        LET m == \CHOOSE y \in S : \A z \in S : y >= z
        IN m

SetMin(S) == 
    IF S = {} THEN CHOOSE x : FALSE 
    ELSE 
        LET m == \CHOOSE y \in S : \A z \in S : y <= z
        IN m

\* 3. Generalized set reduction (fold over a set with an accumulator)
\*    Acc is the initial accumulator value.
\*    Op is a binary operator: Op(acc, elem) returns the new accumulator.
SetReduce(S, Op, Acc) == 
    IF S = {} THEN Acc
    ELSE 
        LET elem == \CHOOSE e \in S : TRUE
        IN SetReduce(S \ {elem}, Op, Op(Acc, elem))

\* 4. Sequence reduction (fold over a sequence with an accumulator)
SeqReduce(seq, Op, Acc) == FoldLeft(Op, Acc, seq)

\* 5. Finding the index (1‑based) of an element in a sequence; returns 0 if not present
SeqIndex(seq, elem) == 
    IF elem \in SeqSet(seq) THEN
        Head({ i \in 1..Len(seq) : seq[i] = elem })
    ELSE 0

\* 6. Converting a sequence to the set of its elements
SeqSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* 7. Getting the last element of a sequence (CHOOSE is safe because Len(seq) > 0)
SeqLast(seq) == 
    IF Len(seq) = 0 THEN CHOOSE x : FALSE
    ELSE seq[Len(seq)]

\* 8. Testing if a sequence is empty
SeqIsEmpty(seq) == Len(seq) = 0

\* 9. Removing all occurrences of an element from a sequence
SeqRemove(seq, elem) == 
    [i \in 1..(Len(seq) - Count(seq, elem)) |-> 
        IF i <= (Count(seq, elem)) THEN 
            seq[i + (Len(seq) - Count(seq, elem))]
        ELSE 
            seq[i - (Count(seq, elem))]]

\* 10. Intersection of a set of sets (S is a set whose elements are themselves sets)
SetOfSetsIntersection(S) == 
    IF S = {} THEN {}
    ELSE \Inter S

\* 11. Generating all permutation sequences of a finite set
\*    We build permutations recursively.
Permutations(S) == 
    IF S = {} THEN { << >> }
    ELSE 
        UNION { 
            [i \in 1..Len(p)+1 |-> 
                IF i <= Len(p) THEN p[i] 
                ELSE e] 
            : e \in S, p \in Permutations(S \ {e}) }

\* 12. Test helper that prints diagnostic information on failure
\*    The operator returns TRUE always; the side‑effect is the print.
Assert(test, msg) == 
    IF test THEN TRUE 
    ELSE (Print(msg); FALSE)

\* ----------------------------------------------------------------------
\*  Required identifiers for the configuration (specified as no‑ops)
\* ----------------------------------------------------------------------
VARIABLE dummy

Init == dummy \in {0}

Next == dummy' = dummy

Spec == Init /\ [][Next]_<<dummy>>

\* The following are just placeholders; they are not used in the .cfg,
\* but the names must exist.
SPECIFICATION == Spec
INIT == Init
NEXT == Next
INVARIANTS == {}
PROPERTIES == {}

====