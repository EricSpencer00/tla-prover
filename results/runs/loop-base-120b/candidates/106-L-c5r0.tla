---- MODULE Util ----
EXTENDS Naturals, Sequences, TLC

(*-----------------------------------------------------------------
  Utility operators for set and sequence manipulation
-----------------------------------------------------------------*)

\* 1. Set intersection test (whether two sets overlap)
SetOverlap(S, T) == ∃ x \in S : x \in T

\* 2. Maximum element selection from a set
SetMax(S) == CHOOSE x \in S : \A y \in S : y <= x

\* 3. Minimum element selection from a set
SetMin(S) == CHOOSE x \in S : \A y \in S : x <= y

\* 4. Generalized set reduction (fold over a set with an accumulator)
SetReduce(S, acc, f) ==
    IF S = {} THEN acc
    ELSE LET e == CHOOSE x \in S IN
         SetReduce(S \ {e}, f(e, acc), f)

\* 5. Sequence reduction (fold over a sequence with an accumulator)
SeqReduce(seq, acc, f) == FoldSeq(seq, acc, f)

\* 6. Finding the index of an element in a sequence (1..Len, 0 if absent)
SeqIndex(seq, elem) ==
    IF elem \in SeqToSet(seq) THEN
        CHOOSE i \in 1..Len(seq) : seq[i] = elem
    ELSE 0

\* 7. Converting a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* 8. Getting the last element of a sequence
SeqLast(seq) == seq[Len(seq)]

\* 9. Testing if a sequence is empty
SeqIsEmpty(seq) == Len(seq) = 0

\* 10. Removing all occurrences of an element from a sequence
SeqRemoveAll(seq, elem) ==
    IF Len(seq) = 0 THEN <<>>
    ELSE IF seq[1] = elem THEN SeqRemoveAll(Rest(seq), elem)
    ELSE <<seq[1]>> \o SeqRemoveAll(Rest(seq), elem)

\* 11. Computing the intersection of a set of sets
SetIntersectionAll(SS) == { x : \A A \in SS : x \in A }

\* 12. Generating all permutation sequences of a finite set
Permutations(S) ==
    IF S = {} THEN { <<>> }
    ELSE UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

\* 13. Test helper for writing assertions that print diagnostic information
TestHelper(cond, msg) ==
    IF cond THEN TRUE ELSE Print(msg) /\ FALSE

====