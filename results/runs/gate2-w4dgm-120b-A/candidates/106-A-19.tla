---- MODULE Util ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
  NONE

\* Returns TRUE iff the two sets share at least one element.
Overlap(s, t) == s \cap t # {}

\* Max and Min of a non-empty set of comparable integers.
MaxElem(S) == CHOOSE x \in S : \A y \in S : y <= x
MinElem(S) == CHOOSE x \in S : \A y \in S : y >= x

\* Generalized reduction (fold) over a set, with an accumulator.
SetReduce(S, f, a) ==
  LET g[T \in SUBSET S] ==
        IF T = {} THEN a
        ELSE LET z == CHOOSE y \in T : TRUE
             IN f[g[T \ {z}], z]
  IN g[S]

SeqReduce(sq, f, a) == FoldSeq(f, a, sq)

IndexOf(sq, x) ==
  CHOOSE i \in DOMAIN sq : sq[i] = x

SeqToSet(sq) == {sq[i] : i \in DOMAIN sq}

LastOf(sq) == IF sq = << >> THEN NONE ELSE sq[Len(sq)]

SeqEmpty(sq) == sq = << >>

RemoveAll(sq, x) ==
  [i \in 1..Len(sq) |-> IF sq[i] = x THEN NONE ELSE sq[i]]

SetIntersection(S) ==
  SetReduce(S, (r, t) => r \cap t, DOMAIN S)

\* Permutations of a set are sequences, so the result lives in Seq(FiniteSets)
Permute(S) == Permutations(S)

\* Test helper: asserts a condition and prints a message on failure.
AssertCondition(p, msg) ==
  IF p THEN TRUE ELSE (Print(msg) /\ FALSE)

====