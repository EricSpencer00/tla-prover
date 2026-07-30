---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences, Integers

CONSTANTS MinSeqLen

ASSUME MinSeqLen \in Nat

\* Intersection test: true iff two sets overlap.
INTERSECT(s1, s2) == \E x \in s1 : x \in s2

\* Maximum element of a non-empty finite set.
MAX(s) == CHOOSE x \in s :
              \A y \in s : y <= x

\* Minimum element of a non-empty finite set.
MIN(s) == CHOOSE x \in s :
              \A y \in s : x <= y

\* Generalized set reduction (fold over a set with an accumulator).
REDUCE(S, f, init) ==
  LET g[T \in SUBSET S] ==
       IF T = {} THEN init
       ELSE LET x == CHOOSE y \in T : TRUE
                rest == g[T \ {x}]
            IN f[x, rest]
  IN g[S]

\* Sequence reduction using the library FoldSeq operator.
SEQREDUCE(seq, f, init) == FoldSeq(f, seq, init)

\* Find the index of an element in a sequence; -1 if absent.
INDEXOF(seq, x) ==
  LET g[i \in 1..Len(seq)] ==
       IF seq[i] = x THEN i ELSE g[i + 1]
  IN IF Len(seq) = 0 THEN -1 ELSE g[1]

\* Convert a sequence to the set of its elements.
SEQSET(seq) == { seq[i] : i \in 1..Len(seq) }

\* Last element of a non-empty sequence, or a placeholder otherwise.
LASTOF(seq) == IF Len(seq) = 0 THEN "empty" ELSE seq[Len(seq)]

\* Test whether a sequence is empty.
ISEMPTY(seq) == Len(seq) = 0

\* Remove all occurrences of an element from a sequence.
RMVALL(seq, x) ==
  LET g[i \in 1..Len(seq)] ==
       IF seq[i] = x THEN g[i + 1] ELSE Append(g[i + 1], seq[i])
  IN IF Len(seq) = 0 THEN << >> ELSE g[1]

\* Intersection of a set of sets.
INTERSECTION(sets) ==
  LET g[T \in SUBSET sets] ==
       IF T = {} THEN {}
       ELSE LET x == CHOOSE y \in T : TRUE
                rest == g[T \ {x}]
            IN x \cap rest
  IN g[sets]

\* Permutations of a finite set: each permutation is a sequence of the set's
\* elements in some order, generated recursively by taking each element as head
\* and permuting the remainder.
PERMUTATIONS(s) ==
  IF s = {} THEN {<< >>}
  ELSE { <<x>> \o p : x \in s, p \in PERMUTATIONS(s \ {x}) }

\* Test helper: prints the diagnostic on failure and always returns TRUE.
TEST(d) == (IF ~d THEN Print("Test failed", d) ELSE TRUE)

\* The module carries the full set of operators of the spec-language subset
\* that the library is intended to expose, even though this library has no
\* actions of its own: the .cfg may still refer to each of these operators.
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE
====