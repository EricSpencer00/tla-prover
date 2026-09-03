---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS MaxVal

\* Set intersection test: TRUE iff the two sets share at least one element.
Intersect(s, t) == \E x \in s : x \in t

\* Maximum element of a non-empty set of natural numbers.
MaxOf(s) == CHOOSE m \in s : \A x \in s : x <= m

\* Minimum element of a non-empty set of natural numbers.
MinOf(s) == CHOOSE m \in s : \A x \in s : m <= x

\* Generalized set reduction (fold) over a set with an accumulator.
FoldSet(f, s, a) ==
  IF s = {} THEN a
  ELSE LET x == CHOOSE y \in s : TRUE IN f[x, FoldSet(f, s \ {x}, a)]

\* Sequence reduction (fold) over a sequence with an accumulator.
FoldSeq(f, seq, a) == IF seq = <<>> THEN a ELSE f[Head(seq), FoldSeq(f, Tail(seq), a)]

\* Find the index of element x in sequence seq (1-based), or 0 if absent.
IndexOf(seq, x) ==
  LET f[i \in 1..Len(seq)] == IF seq[i] = x THEN i ELSE 0 IN
    FoldSeq(f, seq, 0)

\* Convert a sequence to the set of its elements.
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

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
  ELSE LET s == CHOOSE y \in S : TRUE IN s \cap IntersectAll(S \ {s})

\* Generate all permutation sequences of a finite set of natural numbers.
Permutations(s) ==
  IF s = {} THEN { <<>> }
  ELSE { <<x>> \o p : x \in s, p \in Permutations(s \ {x}) }

\* Test helper: asserts a condition, printing a message on failure.
Assert(cond, msg) == IF cond THEN TRUE ELSE msg

\* The module is a library; it has no system state to initialize or transition.
Spec == TRUE
====