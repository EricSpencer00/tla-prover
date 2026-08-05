---- MODULE Util ----
EXTENDS Naturals, FiniteSets

CONSTANTS None

\* SetIntersectionTest: true iff two sets have a non-empty overlap.
SetIntersectionTest(s1, s2) == \E x \in s1 : x \in s2

\* MaxElement / MinElement: compute the maximum or minimum element of a non-empty set.
MaxElement(S) == CHOOSE x \in S : \A y \in S : y <= x
MinElement(S) == CHOOSE x \in S : \A y \in S : y >= x

\* GeneralSetFold: reduce a set using a binary operation and an initial accumulator.
GeneralSetFold(f, base, S) ==
  LET Fold(T) ==
    IF T = {} THEN base
    ELSE LET x == CHOOSE y \in T : TRUE IN f[x, Fold(T \ {x})]
  IN Fold(S)

\* SequenceFold: reduce a sequence using a binary operation and an initial accumulator.
SequenceFold(f, base, seq) == FoldSeq(f, [i \in 1..Len(seq) |-> seq[i]], base)

\* IndexOf: find the index of an element in a sequence, or 0 if not present.
IndexOf(seq, elem) == CHOOSE i \in 0..Len(seq) : (i = 0 /\ \A j \in 1..Len(seq) : seq[j] # elem) \/ (i >= 1 /\ seq[i] = elem)

\* SequenceToSet: the set of elements appearing in a sequence.
SequenceToSet(seq) == {seq[i] : i \in 1..Len(seq)}

\* LastElement: the final element of a non-empty sequence.
LastElement(seq) == seq[Len(seq)]

\* IsSequenceEmpty: true iff a sequence has no elements.
IsSequenceEmpty(seq) == Len(seq) = 0

\* RemoveAll: a sequence with every occurrence of a value removed.
RemoveAll(seq, val) ==
  IF seq = <<>> THEN <<>>
  ELSE IF Head(seq) = val THEN RemoveAll(Tail(seq), val)
  ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), val)

\* SetFamilyIntersection: the intersection of a family of sets (None yields {}).
SetFamilyIntersection(F) ==
  IF F = {} THEN {}
  ELSE LET g[T] ==
         IF T = {} THEN {}
         ELSE LET x == CHOOSE y \in T : TRUE IN IF g(T \ {x}) = {} THEN x ELSE g(T \ {x}) \cap x
       IN g(F)

\* PermutationsOf: the set of all permutation sequences of a finite set.
PermutationsOf(S) ==
  IF S = {} THEN {<<>>}
  ELSE {<<x>> \o p : x \in S, p \in PermutationsOf(S \ {x})}

\* TestHelper: an assertion that prints a diagnostic on failure.
TestHelper(condition, msg) == condition \/ (PrintT(msg) /\ FALSE)

====