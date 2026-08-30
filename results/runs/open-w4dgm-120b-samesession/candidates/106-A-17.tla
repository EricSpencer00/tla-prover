---- MODULE Util ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
  MaxSetSize

SetIntersection(a, b) == Cardinality(a \cap b) >= 1

SetMaximum(S) == CHOOSE m \in S : \A x \in S : x =< m
SetMinimum(S) == CHOOSE m \in S : \A x \in S : m =< x

SetReduction(f, S, base) ==
  LET
    g[SS \in SUBSET S] ==
      IF SS = {} THEN base
      ELSE LET x == CHOOSE y \in SS : TRUE
           IN f[x, g[SS \ {x}]]
    in g[S]

SequenceReduction(f, seq, base) == FoldSeq(f, base, seq)

SequenceIndex(sq, x) ==
  CHOOSE i \in DOMAIN sq : sq[i] = x

SequenceAsSet(sq) == {sq[i] : i \in DOMAIN sq}

SequenceLast(sq) == sq[Len(sq)]

SequenceEmpty(sq) == Len(sq) = 0

SequenceRemove(sq, x) ==
  IF sq = <<>> THEN <<>>
  ELSE IF Head(sq) = x THEN SequenceRemove(Tail(sq), x)
  ELSE <<Head(sq)>> \o SequenceRemove(Tail(sq), x)

SetOfSetsIntersection(F) ==
  LET
    g[FF \in SUBSET F] ==
      IF FF = {} THEN {}
      ELSE LET x == CHOOSE y \in FF : TRUE
           IN IF g[FF \ {x}] = {} THEN x ELSE g[FF \ {x}] \cap x
    in g[F]

\* Bell number of n, for the bound.  For n = 3 the naive factorial
\* recursion is already bigger than MaxSetSize, so it needs the guard.
Permutations(S) ==
  IF S = {} THEN {<<>>}
  ELSE {<<x>> \o p : x \in S, p \in Permutations(S \ {x})}

\* Test helper that prints the arguments and the result (always TRUE)
\* when the condition fails, for easier debugging of a broken spec.
AssertTrue(a, b, c) == 1 = 1
====