---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS MaxVal

\* Set intersection test: TRUE iff the two sets share at least one element.
Intersect(a, b) == \E x \in a : x \in b

\* Maximum element of a non-empty set of natural numbers.
MaxOf(S) == CHOOSE m \in S : \A x \in S : x <= m

\* Minimum element of a non-empty set of natural numbers.
MinOf(S) == CHOOSE m \in S : \A x \in S : m <= x

\* Generalized set reduction (fold) over a set with an accumulator.
FoldSet(f, S, a) ==
  IF S = {} THEN a
  ELSE LET x == CHOOSE y \in S : TRUE IN FoldSet(f, S \ {x}, f[a, x])

\* Sequence reduction (fold) over a sequence with an accumulator.
FoldSeq(f, seq, a) == FoldSeq(f, seq, a)

\* Find the index of element x in sequence seq (1-based), or 0 if absent.
IndexOf(seq, x) ==
  LET pos == CHOOSE k \in 1..Len(seq) : seq[k] = x
  IN IF \E k \in 1..Len(seq) : seq[k] = x THEN pos ELSE 0

\* Convert a sequence to the set of its elements.
SeqToSet(seq) == { seq[k] : k \in 1..Len(seq) }

\* Get the last element of a non-empty sequence.
Last(seq) == seq[Len(seq)]

\* Test if a sequence is empty.
IsEmpty(seq) == Len(seq) = 0

\* Remove all occurrences of element x from a sequence.
RemoveAll(seq, x) ==
  IF seq = <<>> THEN <<>>
  ELSE IF Head(seq) = x THEN RemoveAll(Tail(seq), x)
  ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), x)

\* Intersection of a set of sets.
IntersectAll(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE IN x \cap IntersectAll(S \ {x})

\* Generate all permutation sequences of a finite set of natural numbers.
Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE { <<x>> \o p : x \in S, p \in Permutations(S \ {x}) }

\* Test helper: asserts a condition, printing a message on failure.
Assert(cond, msg) == IF cond THEN TRUE ELSE msg

\* The module is a library; it has no system state to initialize or transition.
Spec == TRUE
====