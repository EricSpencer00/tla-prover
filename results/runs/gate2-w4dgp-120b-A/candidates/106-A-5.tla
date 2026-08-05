---- MODULE Util ----
EXTENDS Integers, Sequences

\* Utility operators for reusable set and sequence logic. No actors or state.

CONSTANTS X,Y

ASSUME X # Y

\* Set intersection exists (s1 and s2 have a common element).
SetIntersects(s1, s2) == \E x \in s1 : x \in s2

\* Maximum element of a non-empty finite set.
SetMax(s) == CHOOSE x \in s : \A y \in s : y <= x

\* Minimum element of a non-empty finite set.
SetMin(s) == CHOOSE x \in s : \A y \in s : x <= y

\* Fold a binary op over a set with an accumulator: op(acc, elem).
FoldSet(s, init, op) ==
  LET rec(T) ==
    IF T = {} THEN init
    ELSE LET x == CHOOSE e \in T : TRUE IN op(rec(T \ {x}), x)
  IN rec(s)

\* Fold a binary op over a sequence: op(acc, seq[i]).
FoldSeq(seq, init, op) == FoldL(seq, init, op)

\* Index of element x in sequence s (1-indexed), or 0 if absent.
SeqIndexOf(s, x) ==
  LET rec(i) ==
    IF i > Len(s) THEN 0
    ELSE IF s[i] = x THEN i
    ELSE rec(i + 1)
  IN rec(1)

\* Convert a sequence to the set of its elements.
SeqToSet(s) == { s[i] : i \in 1..Len(s) }

\* Last element of a non-empty sequence.
SeqLast(s) == s[Len(s)]

\* Is a sequence empty?
SeqEmpty(s) == Len(s) = 0

\* Remove all occurrences of element e from sequence s.
SeqRemoveAll(s, e) ==
  LET rec(i) ==
    IF i > Len(s) THEN << >>
    ELSE IF s[i] = e THEN rec(i + 1)
    ELSE << s[i] >> \o rec(i + 1)
  IN rec(1)

\* Intersection of a set of sets: elements common to all member sets.
SetOfSetsIntersect(S) ==
  { x \in UNION S : \A t \in S : x \in t }

\* Generate every permutation of the set s as a sequence (finite s only).
Permutations(s) ==
  IF s = {} THEN { << >> }
  ELSE
    LET rec(T) ==
      IF T = {} THEN { << >> }
      ELSE { << x >> \o p : x \in T, p \in rec(T \ {x}) }
    IN rec(s)

\* Test helper: assert a condition, printing a message when it fails.
Check(msg, cond) == IF cond THEN TRUE ELSE (Print("FAIL:", msg); FALSE)

====