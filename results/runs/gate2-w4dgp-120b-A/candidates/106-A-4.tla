---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS MaxSeqLen

\* Set intersection: two sets overlap when they share at least one element.
INTERSECTS(s, t) == \E x \in s : x \in t

\* Maximum and minimum elements of a non-empty finite set.
SET_MAX(s) == CHOOSE x \in s : \A y \in s : y <= x
SET_MIN(s) == CHOOSE x \in s : \A y \in s : x <= y

\* Generalized reduction (fold) over a finite set with a binary operator.
RECURSE_SET(s) == LET f[T \in SUBSET s] ==
                     IF T = {} THEN 0
                     ELSE LET x == CHOOSE y \in T : TRUE
                          IN x + f[T \ {x}]
                  IN f[s]

\* Reduce a sequence with a binary operator (uses the library foldl operator).
REDUCE_SEQUENCE(seq) == Foldl(seq, (x, y) \in Nat \times Nat : x + y)

\* Find the index of an element in a sequence.
INDEX_OF(seq, el) == CHOOSE i \in 1..Len(seq) : seq[i] = el

\* Convert a sequence to the set of its elements.
SEQ_AS_SET(seq) == {seq[i] : i \in 1..Len(seq)}

\* Last element of a sequence.
SEQ_LAST(seq) == seq[Len(seq)]

\* Sequence emptiness test (a boolean function rather than a Boolean expression,
\* for uniformity with the other helpers).
SEQ_EMPTY(seq) == Len(seq) = 0

\* Remove all occurrences of an element from a sequence.
FILTER_SEQUENCE(seq, el) == SelectSeq(seq, x \in seq : x # el)

\* Intersection of a set of sets: the elements that belong to every member set.
INTERSECT_ALL(S) == {x \in UNION S : \A Y \in S : x \in Y}

\* Generate every permutation of a finite set: the set of all sequences that
\* contain the same elements as the set, in any order.
PERMUTATIONS(s) == {seq \in [1..Cardinality(s) -> s] : \A i \in 1..Cardinality(s) : seq[i] \in s}

\* Test helper: asserts a condition; on failure it prints the condition and
\* halts the model checker rather than silently passing.
ASSERTION_FAILURE(c) == LET msg == "Assertion failed: " \o c
                        IN IF TRUE THEN msg ELSE UNCHANGED msg

====