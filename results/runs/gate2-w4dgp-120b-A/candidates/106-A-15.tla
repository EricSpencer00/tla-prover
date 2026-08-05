---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS MaxInt

\* Set intersection test: true iff two sets share at least one element.
Intersecting(S, T) == \E x \in S : x \in T

\* Maximum element of a non-empty set.
MaxOf(S) == CHOOSE m \in S : \A x \in S : x <= m

\* Minimum element of a non-empty set.
MinOf(S) == CHOOSE m \in S : \A x \in S : m <= x

\* Generalized set reduction (fold over a set with an accumulator).
ReduceSet(S, f, base) == LET g[T \in SUBSET S] ==
  IF T = {} THEN base
  ELSE LET x == CHOOSE y \in T : TRUE IN f(g[T \ {x}], x) IN g[S]

\* Sequence reduction (fold over a sequence with an accumulator, using a library fold operator).
FoldSeq(seq, f, base) == Fold(f, seq, base)

\* Find the index of element x in sequence s (1-indexed); 0 if not present.
IndexOf(s, x) == IF x \in {s[i] : i \in DOMAIN s}
                 THEN CHOOSE i \in DOMAIN s : s[i] = x
                 ELSE 0

\* Convert a sequence to the set of its elements.
SetOfSeq(s) == {s[i] : i \in DOMAIN s}

\* Get the last element of a non-empty sequence (convenient alias for IndexInSeq(s, Len(s))).
LastOf(s) == s[Len(s)]

\* Test whether a sequence is empty.
SeqIsEmpty(s) == Len(s) = 0

\* Remove all occurrences of element x from sequence s.
RemoveAll(s, x) == LET f[U \in SUBSET DOMAIN s] ==
  IF U = {} THEN <<>>
  ELSE LET i == CHOOSE j \in U : TRUE IN IF s[i] = x THEN f[U \ {i}] ELSE <<s[i]>> \o f[U \ {i}]
  IN f[DOMAIN s]

\* Intersection of a set of sets (join of all members).
SetIntersection(S) == ReduceSet(S, (x, y) \in x \cap y, S)

\* Generate all permutations of a finite set (permutations as sequences).
PermutationSeqs(S) == LET f[T \in SUBSET S] ==
  IF T = {} THEN {<<>>}
  ELSE {<<x>> \o s : x \in T, s \in f[T \ {x}]} IN f[S]

\* Test helper: ASSERT yields a message and a Boolean on failure (not a real operator, just a pattern).
ASSERT(P) == P

====