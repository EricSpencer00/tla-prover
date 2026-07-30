---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS TRUE, FALSE, MaxNat

\* Set intersection test: whether two sets have a common element.
SETINTERSECTION(S, T) == \E x \in S : x \in T

\* Maximum element of a non-empty set.
SETMAX(S) == CHOOSE x \in S : \A y \in S : y <= x

\* Minimum element of a non-empty set.
SETMIN(S) == CHOOSE x \in S : \A y \in S : y >= x

\* Generalized set reduction (fold over a set with an accumulator).
SetReduce(f, S, k) ==
  IF S = {} THEN k
  ELSE LET x == CHOOSE y \in S : TRUE
       IN SetReduce(f, S \ {x}, f(k, x))

\* Sequence reduction (fold over a sequence) via the library fold operator.
SeqReduce(f, seq, k) == Fold(f, k, seq)

\* Find the index of element x in sequence seq; returns 1-based index or 0 if not present.
SeqIndex(seq, x) ==
  LET n == Len(seq)
  IN
    IF n = 0 THEN 0
    ELSE IF Head(seq) = x THEN 1
    ELSE
      LET i == SeqIndex(Tail(seq), x)
      IN IF i = 0 THEN 0 ELSE i + 1

\* Convert a sequence to the set of its elements.
SeqToSet(seq) ==
  IF seq = <<>> THEN {}
  ELSE {Head(seq)} \cup SeqToSet(Tail(seq))

\* Get the last element of a non-empty sequence.
SeqLast(seq) ==
  IF Len(seq) = 1 THEN Head(seq)
  ELSE SeqLast(Tail(seq))

\* Test if a sequence is empty.
SeqEmpty(seq) == Len(seq) = 0

\* Remove all occurrences of element x from sequence seq.
SeqErase(seq, x) ==
  IF seq = <<>> THEN <<>>
  ELSE IF Head(seq) = x THEN SeqErase(Tail(seq), x)
  ELSE <<Head(seq)>> \o SeqErase(Tail(seq), x)

\* Intersection of a set of sets.
SetIntersectionOfSets(S) ==
  IF S = {} THEN {}
  ELSE LET T == CHOOSE t \in S : TRUE
       IN T \cap SetIntersectionOfSets(S \ {T})

\* Generate all permutation sequences of a finite set.
Permutations(S) ==
  IF S = {} THEN {<<>>}
  ELSE { <<x>> \o p : x \in S, p \in Permutations(S \ {x}) }

\* Test helper that prints diagnostic information on failure.
ASSERTPRED(p, msg) == IF p THEN TRUE ELSE msg

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====