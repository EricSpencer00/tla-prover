---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS MaxVal

\* Set intersection test: true iff the two sets share at least one element.
SetIntersection(a, b) == \E x \in a : x \in b

\* Maximum element of a non-empty set.
SetMax(s) == CHOOSE x \in s : \A y \in s : y <= x

\* Minimum element of a non-empty set.
SetMin(s) == CHOOSE x \in s : \A y \in s : x <= y

\* Generalized set reduction: fold a binary operator over a set with an accumulator.
SetReduce(f, s, base) == LET g[T \in SUBSET s] ==
  IF T = {} THEN base
  ELSE LET x == CHOOSE y \in T : TRUE IN f[x, g[T \ {x}]]
  IN g[s]

\* Sequence reduction: fold a binary operator over a sequence with an accumulator.
SeqReduce(f, seq, base) == FoldLeft(f, seq, base)

\* Find the index of an element in a sequence (1-indexed), or 0 if not present.
SeqIndex(seq, x) == LET g[i \in 1..Len(seq)] ==
  IF i > Len(seq) THEN 0
  ELSE IF seq[i] = x THEN i
  ELSE g[i + 1]
  IN g[1]

\* Convert a sequence to the set of its elements.
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* The last element of a non-empty sequence.
SeqLast(seq) == seq[Len(seq)]

\* Test whether a sequence is empty.
SeqEmpty(seq) == Len(seq) = 0

\* Remove all occurrences of an element from a sequence.
SeqRemove(seq, x) == SelectSeq(seq, LAMBDA y : y # x)

\* Intersection of a set of sets.
SetIntersectionAll(S) == SetReduce(SetIntersection, S, {})

\* Generate all permutation sequences of a finite set.
Permutations(S) ==
  IF S = {} THEN { << >> }
  ELSE LET g[T \in SUBSET S] ==
    IF T = {} THEN { << >> }
    ELSE UNION { [x] \o seq : x \in T, seq \in g[T \ {x}] }
    IN g[S]

\* Test helper: asserts a condition and prints a diagnostic message on failure.
Assert(msg, cond) == IF cond THEN TRUE ELSE (Print(msg); FALSE)

====