---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS MaxSet, MaxSeq, NoElem

\* Set intersection test: TRUE iff two sets overlap.
Intersection(s, t) == \E x \in s : x \in t

\* Maximum element of a non-empty finite set.
MaxOf(s) == CHOOSE x \in s : \A y \in s : y <= x

\* Minimum element of a non-empty finite set.
MinOf(s) == CHOOSE x \in s : \A y \in s : x <= y

\* Generalized reduction (fold) over a set, using an accumulator.
SetReduce(s, f, e) == LET
    iter[S \in SUBSET s] ==
        IF S = {} THEN e
        ELSE LET x == CHOOSE y \in S : TRUE IN f(x, iter[S \ {x}])
    IN iter[s]

\* Reduction over a sequence, using the library fold operator.
SeqReduce(seq, f, e) == \E g \in [1..Len(seq) -> {e} \union Range(f)] :
                          g = FoldSeq(seq, f, e)

\* Index of an element in a sequence (0 if absent).
SeqIndex(seq, e) == CHOOSE i \in 0..Len(seq) :
                        (i = 0 \/ (i \in 1..Len(seq) /\ seq[i] = e))

\* Convert a sequence to the set of its elements.
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* The last element of a non-empty sequence.
SeqLast(seq) == seq[Len(seq)]

\* Test if a sequence is empty.
SeqIsEmpty(seq) == Len(seq) = 0

\* Remove all occurrences of an element from a sequence.
SeqRemoveAll(seq, e) == SelectSeq(seq, LAMBDA x : x # e)

\* Intersection of a set of sets, folded with SetReduce.
SetOfSetsIntersect(S) == SetReduce(S, Intersection, MaxSet)

\* Generate all permutations of a finite set as a set of sequences.
PermutationsOf(s) ==
    IF s = {} THEN { << >> }
    ELSE { << x >> \o p : x \in s, p \in PermutationsOf(s \ {x}) }

\* Test helper that prints diagnostic info on failure.
Test(e) ==
    IF e THEN
        TRUE
    ELSE
        /\ Print("Test failed: ")
        /\ UNCHANGED << >>

====