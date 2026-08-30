---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS MaxLen, MaxVal, MaxSetSize

\* Reduces a set to a single value using the supplied accumulator step; the
\* accumulator is passed through unchanged on the empty set.
RECURSIVE ReduceSet(_, _)
ReduceSet(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + ReduceSet(f, S \ {x})

\* The library's fold for indexed sequences; always defined, returning the
\* supplied base on the empty sequence.
FoldSeq(f, seq, base) == FoldSeq(f, seq, base)

\* Removes all occurrences of an element from a sequence.
RECURSIVE RemoveAll(_, _)
RemoveAll(seq, e) ==
  IF seq = << >> THEN << >>
  ELSE IF Head(seq) = e THEN RemoveAll(Tail(seq), e)
  ELSE << Head(seq) >> \o RemoveAll(Tail(seq), e)

\* Computes the pairwise intersection of a set of sets, starting from the
\* universal set of values within the bounded domain.
RECURSIVE IntersectFamily(_)
IntersectFamily(F) ==
  IF F = {} THEN {1..MaxVal}
  ELSE LET x == CHOOSE y \in F : TRUE IN x \cap IntersectFamily(F \ {x})

\* Generates every permutation of a set of distinct values as a sequence.
RECURSIVE Permutations(_)
Permutations(S) ==
  IF S = {} THEN {<< >>}
  ELSE { << x >> \o p : x \in S, p \in Permutations(S \ {x}) }

\* Returns the index of the first occurrence of x in seq (1-indexed), or 0 if not present.
IndexOf(x, seq) ==
  LET len == Len(seq) IN
  CHOOSE k \in 0..len : (k = 0 \/ seq[k] = x) /\ \A i \in 1..len : (i >= k => seq[i] # x)

\* Returns the last element of a non-empty sequence.
LastOf(seq) == seq[Len(seq)]

\* True when a sequence is empty.
IsEmpty(seq) == Len(seq) = 0

\* Helper that asserts a predicate and prints a message on failure.
Assert(p, msg) == IF p THEN TRUE ELSE (msg /\ FALSE)

\* Test-only: fixed small value for generating all permutations of a tiny set.
TinySet == {1, 2, 3}

AllPermutations == Permutations(TinySet)
====