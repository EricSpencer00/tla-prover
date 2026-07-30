---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS MaxVal, MaxLen

\* Set intersection test: true iff the two sets share at least one element.
Intersect(s, t) == \E x \in s : x \in t

\* Maximum element of a non-empty set.
MaxOf(s) == CHOOSE x \in s : \A y \in s : y <= x

\* Minimum element of a non-empty set.
MinOf(s) == CHOOSE x \in s : \A y \in s : x <= y

\* Generalized set reduction: fold a binary operator over a set with an
\* accumulator, visiting the elements in an arbitrary order.
ReduceSet(f, s, a) ==
  IF s = {} THEN a
  ELSE LET x == CHOOSE y \in s : TRUE
       IN ReduceSet(f, s \ {x}, f[a, x])

\* Sequence reduction: fold a binary operator over a sequence with an
\* accumulator, using the library's SeqFold operator.
ReduceSeq(f, seq, a) == SeqFold(f, a, seq)

\* Find the index of an element in a sequence, or 0 if it is absent.
IndexOf(seq, x) ==
  IF seq = <<>> THEN 0
  ELSE IF Head(seq) = x THEN 1
  ELSE LET i == IndexOf(Tail(seq), x)
       IN IF i = 0 THEN 0 ELSE i + 1

\* Convert a sequence to the set of its elements.
SeqToSet(seq) ==
  IF seq = <<>> THEN {}
  ELSE {Head(seq)} \cup SeqToSet(Tail(seq))

\* The last element of a non-empty sequence.
Last(seq) == Head(Reverse(seq))

\* Test whether a sequence is empty.
IsEmpty(seq) == seq = <<>>

\* Remove all occurrences of an element from a sequence.
RemoveAll(seq, x) ==
  IF seq = <<>> THEN <<>>
  ELSE IF Head(seq) = x THEN RemoveAll(Tail(seq), x)
  ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), x)

\* Intersection of a set of sets.
IntersectAll(S) ==
  IF S = {} THEN {}
  ELSE LET s == CHOOSE t \in S : TRUE
       IN s \cap IntersectAll(S \ {s})

\* Generate all permutation sequences of a finite set.
Permutations(s) ==
  IF s = {} THEN {<<>>}
  ELSE {<<x>> \o p : x \in s, p \in Permutations(s \ {x})}

\* Test helper: asserts a condition and prints a diagnostic message on failure.
Assert(cond, msg) == IF cond THEN TRUE ELSE (Print(msg); FALSE)

\* The .cfg file for this module expects no declared identifiers, so the
\* module body is intentionally empty of SPECIFICATION, INIT, NEXT, etc.
====