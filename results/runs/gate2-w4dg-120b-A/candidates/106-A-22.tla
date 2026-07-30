---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS MaxVal, MaxSize, Identity

\* Intersection test: true iff two sets share at least one element.
Intersect(A, B) == \E x \in A : x \in B

\* Maximum element of a non-empty set, returning Identity for the empty set.
MaxElem(S) ==
  IF S = {} THEN Identity
  ELSE LET m == CHOOSE y \in S : \A z \in S : z <= y IN m

\* Minimum element of a non-empty set, returning Identity for the empty set.
MinElem(S) ==
  IF S = {} THEN Identity
  ELSE LET m == CHOOSE y \in S : \A z \in S : y <= z IN m

\* Generalized set reduction: fold an accumulator over the elements of S.
FoldSet(S, f, base) ==
  IF S = {} THEN base
  ELSE LET x == CHOOSE y \in S : TRUE IN f(x, FoldSet(S \ {x}, f, base))

\* Sequence reduction using a library fold (left fold over a sequence of numbers).
DEFINE FoldSeq(f, base, s) == FoldLeft(f, s, base)

\* Find the index of element v in a sequence; returns 0 if v is not present.
IndexOf(s, v) ==
  IF s = <<>> THEN 0
  ELSE IF Head(s) = v THEN 1
  ELSE LET k == IndexOf(Tail(s), v) IN IF k > 0 THEN k + 1 ELSE 0

\* Convert a sequence to the set of its elements.
SeqToSet(s) ==
  IF s = <<>> THEN {}
  ELSE {Head(s)} \cup SeqToSet(Tail(s))

\* Return the last element of a sequence (or Identity for the empty one).
Last(s) ==
  IF s = <<>> THEN Identity
  ELSE IF Tail(s) = <<>> THEN Head(s)
  ELSE Last(Tail(s))

\* Sequence emptiness test.
IsEmpty(s) == s = <<>>

\* Remove all occurrences of element v from a sequence.
RemoveAll(s, v) ==
  IF s = <<>> THEN <<>>
  ELSE IF Head(s) = v THEN RemoveAll(Tail(s), v)
  ELSE <<Head(s)>> \o RemoveAll(Tail(s), v)

\* Intersection of a set of sets; Identity (empty set) if the collection is empty.
IntersectAll(F) ==
  IF F = {} THEN {}
  ELSE LET s == CHOOSE y \in F : TRUE IN s \cap IntersectAll(F \ {s})

\* Generate all permutation sequences of a finite set of size at most MaxSize.
DEFINE Permutations(S) ==
  {p \in Seq(S) : Len(p) = Cardinality(S)}

\* Test helper: asserts a boolean condition, printing a diagnostic message on failure.
Assert(b, msg) == IF b THEN TRUE ELSE Print(msg)

\* The .cfg for this library module expects no public identifiers; all of the above
\* operators exist solely for import by other specifications.
Specification == TRUE
Init == TRUE
Next == TRUE
INVARIANT TRUE
PROPERTY TRUE
====