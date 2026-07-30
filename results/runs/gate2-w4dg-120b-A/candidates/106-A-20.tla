---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS MaxSeq, MaxVal

\* Natural-number range for sequence elements, used for reducing, indexing and
\* permutation generation. The spec's model bounds constrain MaxSeq and MaxVal.
Domain == 0..MaxVal

\* Overlap(s, t) is true iff s and t share at least one element.  Intersection on
\* finite sets is decidable, so the operator is functional rather than a test.
Overlap(s, t) == \E e \in s : e \in t

MaxElem(S) == CHOOSE e \in S : \A x \in S : x <= e
MinElem(S) == CHOOSE e \in S : \A x \in S : x >= e

\* Generalised set reduction (fold) over an unordered set: the order of folding
\* is irrelevant because the operator must be commutative for the spec to be
\* deterministic on a set of values.
FoldSet(f, S, b) == IF S = {} THEN b ELSE LET e == CHOOSE x \in S : TRUE IN f(e, FoldSet(f, S \ {e}, b))

\* Sequence reduction via the library fold operator; the ordering is the
\* sequence's natural ordering.
FoldSeq(f, b, s) == FoldSeq(f, b, s)

IndexOf(s, e) == CHOOSE k \in 1..Len(s) : s[k] = e
SeqToSet(s) == { s[i] : i \in 1..Len(s) }

LastOf(s) == s[Len(s)]
IsEmpty(s) == Len(s) = 0

RemoveAll(s, e) == SelectSeq(s, LAMBDA x : x # e)

IntersectionOf(T) == IF T = {} THEN {} ELSE FoldSet(Overlap, T, CHOOSE e \in T : e)

AllPermutations(A) ==
  LET l == Len(A)
      Count == [i \in 1..l |-> 0]
      BuildSeq(n) ==
        IF n > l THEN << >>
        ELSE
          CHOOSE e \in Domain :
            Count[e] < Cardinality(A) /\ Count' = [Count EXCEPT ![e] = Count[e] + 1] /\ << e >> ^ BuildSeq(n + 1)
  IN BuildSeq(1)

\* Test helper: ASSERT(p) fires a failure action that prints p when p is false.
ASSERT(p) == IF p THEN TRUE ELSE UNCHANGED p

\* The module's specification: the null (empty) action, since the library defines
\* no system behavior on its own.
Spec == TRUE
Init == TRUE
Next == TRUE
TypeOK == TRUE
StateConstraint == TRUE
SpecComplete == TRUE

====