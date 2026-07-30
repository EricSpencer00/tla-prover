---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
  \A, B, C

\* Utility operators for key-value store specs.
\* 1. Set intersection test: true iff x and y overlap.
\* 2. Max/Min element selection from a set.
\* 3. Generalized set reduction (fold over a set).
\* 4. Sequence reduction (fold over a sequence via a library operator).
\* 5. Find the index of an element in a sequence.
\* 6. Convert a sequence to the set of its elements.
\* 7. Get the last element of a sequence.
\* 8. Test if a sequence is empty.
\* 9. Remove all occurrences of an element from a sequence.
\*10. Intersection of a set of sets.
\*11. Generate all permutation sequences of a finite set.
\*12. A test helper printing diagnostics on failure.

RECURSIVE
  ReduceSet(_, _), SetOfSeq(_)

Intersects(x, y) == Cardinality(x \cap y) > 0

Max(x) == CHOOSE e \in x : \A f \in x : e >= f
Min(x) == CHOOSE e \in x : \A f \in x : e <= f

ReduceSet(f, s) ==
  IF s = {} THEN 0
  ELSE LET e == CHOOSE x \in s : TRUE IN f[e] + ReduceSet(f, s \ {e})

SeqReduce(f, s) == FoldSeq(f, s)

IndexOf(v, s) == CHOOSE i \in DOMAIN s : s[i] = v

SetOfSeq(s) ==
  IF s = <<>> THEN {}
  ELSE {s[1]} \cup SetOfSeq(Tail(s))

LastOfSeq(s) == s[Len(s)]

IsEmpty(s) == s = <<>>

RemoveAll(v, s) ==
  IF s = <<>> THEN <<>>
  ELSE IF s[1] = v THEN RemoveAll(v, Tail(s)) ELSE <<s[1]>> \o RemoveAll(v, Tail(s))

IntersectSets(S) == IF S = {} THEN {} ELSE \A x \in S : x \cap Select(S) = IntersectSets(S \ {Select(S)})

Permutations(S) ==
  IF S = {} THEN {<<>>}
  ELSE { <<e>> \o s : e \in S, s \in Permutations(S \ {e}) }

TestHelper(cond, msg) == IF cond THEN TRUE ELSE (Print(msg); FALSE)

====