---- MODULE Util ----
EXTENDS Naturals, Sequences

CONSTANTS S1, S2, S3, S4

\* Intersection test: two sets overlap iff their intersection is non-empty.
SetOverlap(s, t) == {x \in s : x \in t} # {}

\* Max/min (any choice if not unique) of a non-empty finite set of naturals.
SetMax(s) == CHOOSE x \in s : \A y \in s : y =< x
SetMin(s) == CHOOSE x \in s : \A y \in s : x =< y

\* Generalized fold over a set.
SetReduce(f, s, base) ==
  IF s = {}
  THEN base
  ELSE LET y == CHOOSE x \in s : TRUE IN f(y, SetReduce(f, s \ {y}, base))

\* Fold over a sequence via the library's ReduceSeq operator.
SeqReduce(f, seq, base) == ReduceSeq(f, seq, base)

\* Index of an element in a sequence (0 means not present).
SeqIndex(s, e) ==
  LET k == CHOOSE k \in 1..Len(s) : s[k] = e
  IN IF \E j \in 1..Len(s) : s[j] = e THEN k ELSE 0

\* Convert a sequence to the set of its elements.
SeqToSet(s) == {s[k] : k \in 1..Len(s)}

\* Last element of a non-empty sequence.
SeqLast(s) == s[Len(s)]

\* Test if a sequence is empty.
SeqIsEmpty(s) == Len(s) = 0

\* Remove all occurrences of e from a sequence.
SeqRemoveAll(s, e) ==
  IF s = <<>> THEN <<>>
  ELSE IF Head(s) = e THEN SeqRemoveAll(Tail(s), e)
  ELSE <<Head(s)>> \o SeqRemoveAll(Tail(s), e)

\* Intersection of a set of sets.
IntersectAll(X) == SetReduce((a, b) |-> a \cap b, X, S1 \cup S2 \cup S3 \cup S4)

\* Generate all permutations of a finite set via recursion on the set.
Permutations(s) ==
  IF s = {}
  THEN {<<>>}
  ELSE { <<x>> \o p : x \in s, p \in Permutations(s \ {x}) }

\* Test helper: asserts p and prints a message on failure.
Test(p, msg) == IF p THEN TRUE ELSE (msg /\ FALSE)

\* The spec below is a placeholder; this module is a library with no system model.
SPEC == TRUE
INIT == TRUE
NEXT == UNCHANGED << >>
INVARIANTS == {}
PROPERTIES == {}
====