---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS

ASSUME

ASSUME

ASSUME

ASSUME

ASSUME

ASSUME

ASSUME

ASSUME

ASSUME

ASSUME

ASSUME

ASSUME

ASSUME

ASSUME

ASSUME

ASSUME
\* Utility module for the key-value store project.  It carries a small
\* suite of pure helper operators -- set intersection, folding over
\* sets and sequences, converting between sequences and sets, and a
\* permutation generator -- and is imported by the store's other
\* specifications.  It has no system state of its own.

\* Set intersection: true iff the two argument sets share at least one element.
Intersecting(S, T) == \E x \in S : x \in T

\* Set reduction: fold the binary operator 'op' over the elements of set S,
\* starting from the accumulator 'base'.  Because sets are unordered this
\* defines the reduction in a way that does not depend on any iteration order.
ReduceSet(S, op, base) ==
  LET fold(T) ==
       IF T = {} THEN base
       ELSE LET x == CHOOSE y \in T : TRUE IN op[x, fold(T \ {x})]
  IN fold(S)

\* Sequence reduction: fold the binary operator 'op' over the sequence s,
\* left to right, starting from the accumulator 'base'.  This uses the
\* library's FoldSeq operator to do the iteration.
ReduceSeq(s, op, base) == FoldSeq(s, op, base)

\* Index of an element in a sequence: the position of x in s, or 0 if x is
\* not present.  Positions in a sequence are 1-indexed here.
IndexOf(s, x) ==
  LET i == CHOOSE y \in {1, 2, ..., Len(s)} : s[y] = x
  IN IF \E y \in {1, 2, ..., Len(s)} : s[y] = x THEN i ELSE 0

\* Sequence to set: the set containing exactly the values that appear in s.
SeqToSet(s) == {s[i] : i \in 1 .. Len(s)}

\* Last element of a sequence.
SeqLast(s) == s[Len(s)]

\* Empty-sequence test.
SeqEmpty(s) == Len(s) = 0

\* Remove all occurrences of x from sequence s.
SeqRemoveAll(s, x) == SelectSeq(s, LAMBDA y : y # x)

\* Intersection of a set of sets: the elements common to every set in coll.
SetOfSetsIntersection(coll) ==
  LET fold(T) ==
       IF T = {} THEN {}
       ELSE LET x == CHOOSE y \in T : TRUE IN x \cap fold(T \ {x})
  IN fold(coll)

\* Permutations of a finite set: all sequences containing exactly the
\* elements of the set, each exactly once.  Enumerated recursively by
\* inserting each element into every position of the permutations of the
\* remaining elements.
Permutations(S) ==
  IF S = {} THEN <<>>
  ELSE IF Cardinality(S) = 1 THEN << <<CHOOSE x \in S : TRUE>> >>
  ELSE
    { seq \in UNION { InsertAt(i, x, p) :
        p \in Permutations(S \ {x}) :
        i \in 1 .. Len(p) + 1 } : x \in S }

\* Insert the value 'v' into sequence 's' at position 'i'.
InsertAt(i, v, s) == SubSeq(s, 1, i - 1) \cup <<v>> \cup SubSeq(s, i, Len(s))

\* Test helper that prints a message and always returns FALSE; used in
\* asserts so a failing test prints its diagnostic payload.
FailTest(msg) == PrintT(msg) /\ FALSE

====