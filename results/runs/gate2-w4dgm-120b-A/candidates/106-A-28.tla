---- MODULE Util ----
EXTENDS Sequences, FiniteSets

CONSTANTS MaxLen

\* Set overlap test: are two sets non-disjoint?
SetIntersection(s, t) == \E x \in s : x \in t

\* Max and min element of a non-empty finite set.
SetMax(s) == CHOOSE x \in s : \A y \in s : y <= x
SetMin(s) == CHOOSE x \in s : \A y \in s : x <= y

\* Generalized fold/reduction over a set with an accumulator.
SetReduce(f, s, a) ==
  IF s = {} THEN a
  ELSE LET x == CHOOSE y \in s : TRUE IN f[x, SetReduce(f, s \ {x}, a)]

\* Reduce a sequence via a supplied fold operator.
SeqReduce(op, seq, a) == FOLDA(op, seq, a)

\* Index of an element in a sequence, or Len(seq) if absent.
SeqIndex(seq, x) ==
  LET pos == { k \in 1..Len(seq) : seq[k] = x }
  IN IF pos = {} THEN Len(seq) ELSE CHOOSE k \in pos : TRUE

SeqSet(seq) == { seq[k] : k \in 1..Len(seq) }

Last(seq) == seq[Len(seq)]
SeqEmpty(seq) == Len(seq) = 0

RemoveAll(seq, x) ==
  IF seq = <<>> THEN seq
  ELSE IF Head(seq) = x THEN RemoveAll(Tail(seq), x)
  ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), x)

SetIntersectionOfSets(ss) == { x \in UNION ss : \A t \in ss : x \in t }

\* Generate all permutations of a finite set, each as a sequence.
Permutations(s) ==
  IF s = {} THEN { <<>> }
  ELSE { <<x>> \o p : x \in s, p \in Permutations(s \ {x}) }

\* Test helper that prints diagnostics on failure.
TestHelper(guard, msg) == IF guard THEN "ok" ELSE "FAIL: " \o msg

====