---- MODULE Util ----
EXTENDS FiniteSets, Sequences, TLC

\* ----------------------------------------------------------------------
\* Utility library providing common helper operators for set and sequence
\* manipulation.  The module defines the following operators:
\*   Overlap           : set intersection test
\*   MaxInSet, MinInSet: maximum and minimum element selection from a set
\*   ReduceSet         : generalized set reduction (fold over a set)
\*   ReduceSeq         : sequence reduction using a library fold operator
\*   IndexOf           : find the index of an element in a sequence
\*   SeqToSet          : convert a sequence to the set of its elements
\*   Last              : get the last element of a non‑empty sequence
\*   IsEmptySeq        : test if a sequence is empty
\*   RemoveAll         : remove all occurrences of an element from a sequence
\*   IntersectAll      : intersection of a set of sets
\*   Permutations      : generate all permutation sequences of a finite set
\*   Assert            : test helper that prints diagnostic information on failure
\* ----------------------------------------------------------------------


\*-----------------------------------------------------------------------
\* 1. Set intersection test – true iff two sets share at least one element
\*-----------------------------------------------------------------------
Overlap(S, T) ==  ~ (S \cap T = {})
                          
\*-----------------------------------------------------------------------
\* 2. Maximum and minimum element selection from a non‑empty finite set
\*-----------------------------------------------------------------------
\* We use the standard ordering on natural numbers.  For sets that may
\* contain other comparable values, a custom ordering would be needed.
MaxInSet(S) ==
    IF S = {} THEN
        CHOOSE x \in {}: TRUE \* undefined for empty set, raises error
    ELSE
        \E x \in S: \A y \in S: y <= x

MinInSet(S) ==
    IF S = {} THEN
        CHOOSE x \in {}: TRUE \* undefined for empty set, raises error
    ELSE
        \E x \in S: \A y \in S: x <= y

\*-----------------------------------------------------------------------
\* 3. Generalized set reduction (fold) with an accumulator
\*-----------------------------------------------------------------------
\* ReduceSet(f, init, S) folds the binary operator f over the elements of
\* the finite set S, starting with accumulator init.  The order is nondeterministic
\* but the result is well‑defined when f is associative and commutative.
ReduceSet(f, init, S) ==
    IF S = {} THEN init
    ELSE
        LET
            Fold(Acc, Rest) ==
                IF Rest = {} THEN Acc
                ELSE
                    \E e \in Rest:
                        Fold(f(Acc, e), Rest \ {e})
        IN
            Fold(init, S)

\*-----------------------------------------------------------------------
\* 4. Sequence reduction using the library FoldSeq operator
\*-----------------------------------------------------------------------
\* FoldSeq is defined in the Sequences module as a left‑fold over a sequence.
ReduceSeq(f, init, seq) == FoldSeq(f, init, seq)

\*-----------------------------------------------------------------------
\* 5. Find the index (1‑based) of an element in a sequence
\*-----------------------------------------------------------------------
IndexOf(seq, elem) ==
    IF elem \in ran(seq) THEN
        \E i \in 1..Len(seq) : seq[i] = elem
    ELSE
        0

\*-----------------------------------------------------------------------
\* 6. Convert a sequence to the set of its elements
\*-----------------------------------------------------------------------
SeqToSet(seq) == ran(seq)

\*-----------------------------------------------------------------------
\* 7. Get the last element of a non‑empty sequence
\*-----------------------------------------------------------------------
Last(seq) ==
    IF Len(seq) = 0 THEN
        CHOOSE x \in {}: TRUE \* undefined for empty sequence
    ELSE
        seq[Len(seq)]

\*-----------------------------------------------------------------------
\* 8. Test if a sequence is empty
\*-----------------------------------------------------------------------
IsEmptySeq(seq) == Len(seq) = 0

\*-----------------------------------------------------------------------
\* 9. Remove all occurrences of an element from a sequence
\*-----------------------------------------------------------------------
RemoveAll(seq, elem) ==
    [ i \in 1..(Len(seq) - CountOccurrences(seq, elem)) |-> 
        seq[ i + CountBefore(seq, elem, i) ] ]

CountOccurrences(seq, elem) ==
    Cardinality({ i \in 1..Len(seq) : seq[i] = elem })

CountBefore(seq, elem, i) ==
    Cardinality({ j \in 1..(i-1) : seq[j] = elem })

\*-----------------------------------------------------------------------
\* 10. Intersection of a set of sets
\*-----------------------------------------------------------------------
IntersectAll(SS) ==
    IF SS = {} THEN {}
    ELSE
        \CHOOSE s \in SS : 
            \A t \in SS : s \subseteq t

\*-----------------------------------------------------------------------
\* 11. Generate all permutation sequences of a finite set
\*-----------------------------------------------------------------------
\* PermutationsOfSet(S) returns the set of all sequences that are
\* permutations of the elements of S.  S must be finite.
PermutationsOfSet(S) ==
    IF S = {} THEN {<<>>}
    ELSE
        { <<e>> \o p : e \in S, p \in PermutationsOfSet(S \ {e}) }

\*-----------------------------------------------------------------------
\* 12. Assertion helper that prints diagnostic information on failure
\*-----------------------------------------------------------------------
\* The Assert operator evaluates a boolean condition.  If the condition is
\* false, it prints the supplied message and aborts the model checking run.
Assert(cond, msg) ==
    IF cond THEN TRUE
    ELSE
        BEGIN
            Print(msg);
            FALSE
        END

\*-----------------------------------------------------------------------
\* 13. Stub specification required by the task description
\*-----------------------------------------------------------------------
SPECIFICATION == TRUE
INIT == TRUE
NEXT == UNCHANGED << >>
INVARIANTS == {}
PROPERTIES == {}

=============================================================================