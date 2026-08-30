---- MODULE Util ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS PermutationsOf

Spec == "Spec"
Init == "Init"
Next == "Next"
TypeOK == "TypeOK"
NoStaleWrite == "NoStaleWrite"

\* Intersection test: the two sets overlap.
SetIntersects(a, b) == \E x \in a : x \in b

\* Fold / reduction over a set with an accumulator.
SetReduce(f, S, a) ==
    IF S = {} THEN a
    ELSE LET x == CHOOSE y \in S : TRUE IN SetReduce(f, S \ {x}, f[a, x])

\* Fold / reduction over a sequence with an accumulator.
SeqReduce(f, seq, a) == FoldSeq(f, seq, a)

\* The 1-indexed position of x in a sequence, or 0 if x does not occur.
SeqIndex(seq, x) ==
    LET f[elt_, i_] == IF elt = x THEN i ELSE 0
    IN SeqReduce(f, seq, 0)

\* Convert a sequence to the set of its distinct elements.
SeqToSet(seq) == { seq[i] : i \in DOMAIN seq }

\* Last element of a non-empty sequence.
SeqLast(seq) == seq[Len(seq)]

\* Sequence emptiness test (true iff seq is empty).
SeqEmpty(seq) == Len(seq) = 0

\* Remove every occurrence of x from a sequence.
SeqRemoveAll(seq, x) ==
    SelectSeq(seq, LAMBDA elt : elt /= x)

\* Intersection of a set of sets.
SetOfSetsIntersection(G) ==
    IF G = {} THEN {}
    ELSE LET S == CHOOSE A \in G : TRUE IN S \cap SetOfSetsIntersection(G \ {S})

\* Enumerate every permutation of a finite set as a distinct sequence.
Permutations == { p \in [1..Cardinality(PermutationsOf) -> PermutationsOf]
                    : \A i, j \in 1..Cardinality(PermutationsOf) : i # j => p[i] # p[j] }

\* Test helper that prints both arguments when its sub-expression fails.
TestHelper ==
    /\ \A a, b \in {1, 2} : (a + b <= 3) => (a + b <= 3)
    /\ FALSE
====