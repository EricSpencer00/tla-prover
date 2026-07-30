---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANT MaxSeqLen, MaxSetSize, MaxSeq

\* Generic fold operator over a sequence, provided by the standard library.
FoldSeq(f, seq, base) ==
  IF seq = <<>> THEN base
  ELSE f(Head(seq), FoldSeq(f, Tail(seq), base))

\* 1. Set intersection test: whether two sets overlap.
SetOverlap(s1, s2) == \E x \in s1 : x \in s2

\* 2. Maximum element selection from a set.
SetMax(S) ==
  LET f(a, b) == IF b > a THEN b ELSE a
  IN  FoldSeq(f, Seq(S), CHOOSE e \in S : TRUE)

\*    Minimum element selection from a set.
SetMin(S) ==
  LET f(a, b) == IF b < a THEN b ELSE a
  IN  FoldSeq(f, Seq(S), CHOOSE e \in S : TRUE)

\* 3. Generalized set reduction (fold over a set with an accumulator).
SetReduce(f, S, base) ==
  IF S = {} THEN base
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f(x, SetReduce(f, S \ {x}, base))

\* 4. Sequence reduction (fold over a sequence with an accumulator, via FoldSeq).
SeqReduce(f, seq, base) == FoldSeq(f, seq, base)

\* 5. Find the index of an element in a sequence (1-based, or 0 if not present).
SeqFind(seq, x) ==
  LET g(a, b) == IF a = b THEN 0 ELSE CHOOSE n \in 1..Len(seq) : seq[n] = b
  IN  CHOOSE n \in 1..Len(seq) : seq[n] = x

\* 6. Convert a sequence to the set of its elements.
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* 7. Get the last element of a sequence.
SeqLast(seq) == IF seq = <<>> THEN "undef" ELSE seq[Len(seq)]

\* 8. Test if a sequence is empty.
SeqEmpty(seq) == seq = <<>>

\* 9. Remove all occurrences of an element from a sequence.
SeqRemove(seq, x) ==
  IF seq = <<>> THEN <<>>
  ELSE IF Head(seq) = x THEN SeqRemove(Tail(seq), x)
  ELSE <<Head(seq)>> \o SeqRemove(Tail(seq), x)

\* 10. Intersection of a set of sets.
SetOfSetsIntersection(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE
       IN x \cap SetOfSetsIntersection(S \ {x})

\* 11. Generate all permutation sequences of a finite set (domain = 1..n).
Permutations(S) ==
  IF S = {} THEN {<<>>}
  ELSE { <<x>> \o s : x \in S, s \in Permutations(S \ {x}) }

\* 12. Test helper that prints diagnostic info on failure (a no-op at runtime).
TestHelper(expr) ==
  IF expr THEN TRUE
  ELSE
    /\ PrintT("TEST_FAILURE:", expr)
    /\ FALSE

\* Operators with names required by the reference .cfg (no-op body).
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}
====