---- MODULE Util ----
EXTENDS Sequences

CONSTANTS Sets, Sep

\* Intersection test: are two sets non-disjoint?
Intersect(s1, s2) == \E a \in s1 : a \in s2

\* Max/min element selection from a finite set via reduction.
ReduceSet(s, f) == IF s = {} THEN Sep ELSE f(CHOOSE x \in s : TRUE, ReduceSet(s \ {CHOOSE x \in s : TRUE}, f))
MaxSet(s) == ReduceSet(s, [x, y \in Sets |-> IF x > y THEN x ELSE y])
MinSet(s) == ReduceSet(s, [x, y \in Sets |-> IF x < y THEN x ELSE y])

\* Generalized reduction (fold) over a set with an accumulator.
FoldSet(f, acc, s) == IF s = {} THEN acc ELSE
  LET x == CHOOSE y \in s : TRUE
  IN FoldSet(f, f(acc, x), s \ {x})

\* Fold over a sequence (via the standard library Sequencing's FoldL).
FoldSeq(f, acc, seq) == FoldL(f, seq, acc)

\* Index of an element in a sequence (1-based per TLA+ convention).
IndexOf(seq, a) == CHOOSE k \in DOMAIN seq : seq[k] = a

\* Convert a sequence to the set of its elements.
Elems(seq) == { seq[i] : i \in DOMAIN seq }

\* Get the last element of a non-empty sequence.
SeqLast(seq) == seq[Len(seq)]

IsSeqEmpty(seq) == seq = << >>

\* Remove all occurrences of an element from a sequence.
Except(seq, a) == SelectSeq(seq, LAMBDA x : x # a)

\* Intersection over a set of sets.
IntersectOver(sets) == CHOOSE s \in sets : \A t \in sets : Intersect(s, t)

\* Permutations of a finite set: a set of sequences covering every ordering.
Permutations(sets) == { f[1..Cardinality(sets)] : f \in [1..Cardinality(sets) -> sets]
  /\ \A i, j \in 1..Cardinality(sets) : (i # j) => (f[i] # f[j]) }

TestHelper(cond) == IF cond THEN "PASS" ELSE "FAIL"

Spec == TRUE
Init == TRUE
Next == TRUE
INVar == Spec
Property == Spec
====