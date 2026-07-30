---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Part, MaxPart

\* set intersection test: whether two sets overlap
Overlap(S, T) == \E x \in S : x \in T

\* maximum element selection from a set
MaxOf(S) == CHOOSE x \in S : \A y \in S : y <= x

\* minimum element selection from a set
MinOf(S) == CHOOSE x \in S : \A y \in S : y >= x

\* generalized set reduction (fold over a set with an accumulator)
SetReduce(f, S, a) ==
  IF S = {} THEN a
  ELSE LET x == CHOOSE y \in S : TRUE IN SetReduce(f, S \ {x}, f[a, x])

\* sequence reduction (fold over a sequence with an accumulator)
SeqReduce(f, seq, a) == SeqReduce(f, Rest(seq), f[a, Head(seq)])

\* finding the index of an element in a sequence
SeqIndex(seq, x) ==
  IF seq = << >> THEN 0
  ELSE IF Head(seq) = x THEN 1
  ELSE LET i == SeqIndex(Rest(seq), x) IN IF i = 0 THEN 0 ELSE i + 1

\* converting a sequence to the set of its elements
SeqToSet(seq) == { x \in Part : SeqIndex(seq, x) > 0 }

\* getting the last element of a sequence
SeqLast(seq) == Head(Rev(seq))

\* testing if a sequence is empty
SeqEmpty(seq) == seq = << >>

\* removing all occurrences of an element from a sequence
SeqRemove(seq, x) ==
  IF seq = << >> THEN << >>
  ELSE IF Head(seq) = x THEN SeqRemove(Rest(seq), x)
  ELSE << Head(seq) >> \o SeqRemove(Rest(seq), x)

\* intersection of a set of sets
InterOf(P) ==
  IF P = {} THEN Part
  ELSE LET S == CHOOSE s \in P : TRUE IN S \cap InterOf(P \ {S})

\* generate all permutation sequences of a set
Permutations(S) ==
  IF S = {} THEN { << >> }
  ELSE { << x >> \o p : x \in S, p \in Permutations(S \ {x}) }

\* test helper that prints a diagnostic message before asserting a condition
TestHelper(cond, msg) == IF cond THEN TRUE ELSE PrintT(msg) /\ FALSE

\* Required no-op operators (the .cfg has no required identifiers, but they must
\* be present by name in this module so the spec is syntactically complete).
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====