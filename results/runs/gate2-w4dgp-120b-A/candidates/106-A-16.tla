---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

\* This is a utility library module providing common helper operators used by the key-value
\* store specifications.  It defines reusable operators for set and sequence manipulation,
\* including set intersection, reduction, indexing, permutation generation, and a test helper.
\* The module itself has no actors, no system components, no variables, and no actions; it
\* only exports its operators.

CONSTANTS MaxSeqLen, PermuteDebug

\* Test helper: Assert(action) runs the action and, if it returns FALSE, prints a
\* diagnostic message instead of simply aborting the model check.  This is handy inside
\* properties where a failed test does not otherwise generate a failure trace.
Assert(f) == IF f THEN TRUE ELSE (Print("ASSERTION FAILED"); FALSE)

\* SetIntsect(S, T): two sets overlap if they share at least one element.
SetIntsect(S, T) == \E x \in S : x \in T

\* MaxElem(S): greatest element of a non-empty finite set of naturals; MinElem the least.
MaxElem(S) == CHOOSE m \in S : \A x \in S : x <= m
MinElem(S) == CHOOSE m \in S : \A x \in S : m <= x

\* SetReduce(S, f, base): fold a binary function f over a set S, starting from base.
SetReduce(S, f, base) == LET Red(X) ==
  IF X = {} THEN base
  ELSE LET x == CHOOSE y \in X : TRUE IN f[x, Red(X \ {x})]
  IN Red(S)

\* SeqReduce(seq, f, base): fold a binary function f over a sequence seq, left-to-right.
SeqReduce(seq, f, base) == FoldLeft(f, seq, base)

\* SeqIndex(s, i): the element at position i in a sequence s (1-indexed), or 0 if out of range.
SeqIndex(s, i) == IF i >= 1 /\ i <= Len(s) THEN s[i] ELSE 0

\* AsSet(s): the set of all elements appearing in the sequence s.
AsSet(s) == {s[i] : i \in 1..Len(s)}

\* LastOf(s): the final element of a non-empty sequence.
LastOf(s) == s[Len(s)]

\* Empty(s): true iff the sequence s has length zero.
Empty(s) == Len(s) = 0

\* RemoveAll(s, x): the sequence s with every occurrence of x excised.
RemoveAll(s, x) == [i \in 1..(Len(s) - Cardinality({j \in 1..Len(s) : s[j] = x}))
                     |-> s[CHOOSE k \in 1..Len(s) : s[k] # x /\ Cardinality({j \in 1..k : s[j] = x}) = i - 1]]

\* IntersectOf(S): the intersection of every set in S.
IntersectOf(S) == IF S = {} THEN {} ELSE {x \in CHOOSE y \in S : TRUE : \A t \in S : x \in t}

\* PermutationsOf(T): all permutation sequences of the finite set T.
\* This is a recursive definition over the size of T, bounded by MaxSeqLen.
PermutationsOf(T) ==
  IF T = {} THEN {<<>>}
  ELSE LET rec(S) ==
    IF S = {} THEN {<<>>}
    ELSE { <<e>> \o p : e \in S, p \in rec(S \ {e}) }
    IN rec(T)

\* Assertion test: each utility operator returns the expected value on a sample input.
OperatorsTest ==
  /\ Assert(~SetIntsect({1, 2}, {3, 4}))
  /\ Assert(SetIntsect({1, 2}, {2, 3}))
  /\ Assert(MaxElem({1, 3, 2}) = 3)
  /\ Assert(MinElem({1, 3, 2}) = 1)
  /\ Assert(SetReduce({1, 2, 3}, LAMBDA a, b : a + b, 0) = 6)
  /\ Assert(SeqReduce(<<1, 2, 3>>, LAMBDA a, b : a + b, 0) = 6)
  /\ Assert(SeqIndex(<<2, 3>>, 1) = 2)
  /\ Assert(SeqIndex(<<2, 3>>, 3) = 0)
  /\ Assert(AsSet(<<1, 2, 1>>) = {1, 2})
  /\ Assert(LastOf(<<1, 2, 3>>) = 3)
  /\ Assert(Empty(<<>>))
  /\ ~Empty(<<0>>)
  /\ Assert(RemoveAll(<<1, 2, 1>>, 1) = <<2>>)
  /\ Assert(IntersectOf({{1, 2}, {2, 3}}) = {2})
  /\ Assert(PermutationsOf({1, 2}) = {<<1, 2>>, <<2, 1>>})

INVARIANT OperatorsTest

====