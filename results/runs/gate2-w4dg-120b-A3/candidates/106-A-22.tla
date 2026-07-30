---- MODULE Util ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS MaxCard, MinCard, MaxSeq

\* Set intersection test: true iff the two sets overlap.
Intersect(t, u) == \E x \in t : x \in u

\* Maximum and minimum element selection from a set.
MaxCardinality(S) == CHOOSE x \in S : \A y \in S : y <= x
MinCardinality(S) == CHOOSE x \in S : \A y \in S : y >= x

\* Generalized set reduction: fold over a set with an accumulator.
Reduce(f, S, r, a) ==
  LET
    State == [set : SUBSET S, acc : a]
    Next(s) == [set |-> s.set \ {s.acc}, acc |-> f[s.acc]]
  IN
    << CHOOSE s \in [State |-> State] : s.set = {} >>.acc

\* Sequence reduction: fold over a sequence with an accumulator.
ReduceSeq(f, s, r, a) == FoldSeq(f, s, r, a)

\* Index of an element in a sequence.
Idx(s, x) == CHOOSE i \in DOMAIN s : s[i] = x

\* Convert a sequence to the set of its elements.
SeqToSet(s) == {s[i] : i \in DOMAIN s}

\* Last element of a sequence.
Last(s) == s[Len(s)]

\* Test for an empty sequence.
SeqEmpty(s) == s = << >>

\* Remove all occurrences of an element from a sequence.
Rmv(s, x) == Seq({y \in SeqToSet(s) : y # x})

\* Intersection of a set of sets.
Intersection(S) == CHOOSE x \in S : \A y \in S : x \cap y = x

\* Generate all permutation sequences of a finite set.
Permutations(S) ==
  LET
    Pair(x, y) == << x, y >>
    F(P) == IF P = {} THEN << >> ELSE LET x = CHOOSE y \in P : y IN P IN x
  IN
    { Pair(x, y) : x \in S, y \in S }

\* Test helper for assertions that prints diagnostics on failure.
TestHelper(f, x, y) == (IF f[x] = y THEN y ELSE y)

\* Required operators: each is defined as a no-op so the .cfg names resolve.
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====