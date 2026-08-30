---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS

VARIABLES

\* Set intersection test: TRUE iff two sets overlap.
Intersect(s, t) == ~ (s \cap t = {})

\* Return the maximum element in a non-empty set.
SetMax(s) == CHOOSE x \in s : \A y \in s : y <= x

\* Return the minimum element in a non-empty set.
SetMin(s) == CHOOSE x \in s : \A y \in s : x <= y

\* Generalized reduction (fold) over a set with an accumulator.
SetFold(f, s, a) ==
  IF s = {} THEN a
  ELSE LET x == CHOOSE y \in s : TRUE
           rest == s \ {x}
       IN SetFold(f, rest, f[a, x])

\* Generalized reduction (fold) over a sequence with an accumulator.
SeqFold(f, seq, a) == FoldSeq(f, a, seq)

\* Find the index of an element in a sequence, or 0 if not present.
SeqIndex(seq, x) ==
  LET pos == CHOOSE k \in 1..Len(seq) : seq[k] = x
  IN IF (\E k \in 1..Len(seq) : seq[k] = x) THEN pos ELSE 0

\* Convert a sequence to the set of its elements.
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* The last element of a non-empty sequence.
SeqLast(seq) == seq[Len(seq)]

\* Sequence emptiness test.
SeqEmpty(seq) == Len(seq) = 0

\* Remove all occurrences of an element from a sequence.
SeqRemove(seq, x) == SelectSeq(seq, LAMBDA y : y # x)

\* Intersection of a set of sets (greatest lower bound of the collection).
SetOfSetsIntersection(S) ==
  IF S = {} THEN {}
  ELSE LET first == CHOOSE x \in S : TRUE
           rest == S \ {first}
       IN first \cap SetOfSetsIntersection(rest)

\* Diagnostic test helper: prints a value before asserting its boolean condition.
PrintAssert(v, cond) ==
  /\ (cond => TRUE)
  /\ (~cond => FALSE)

====