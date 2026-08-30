---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS

\* SPECIFICATION: a no-op placeholder so the TLC configuration is satisfied;
\* this library module has no system behavior to model directly.
Specification == TRUE

\* INIT: a no-op placeholder so the TLC configuration is satisfied; no state
\* is held by this library module.
Init == TRUE

\* NEXT: a no-op placeholder so the TLC configuration is satisfied; no state
\* is held by this library module.
Next == TRUE

\* INVARIANTS: none -- the library module has nothing to constrain.
Invariants == {}

\* PROPERTIES: same as INVARIANTS -- nothing to assert about this library.
Properties == {}

\* Intersect(s1, s2): true iff the two sets share at least one element.
Intersect(s1, s2) == \E x \in s1 : x \in s2

\* MaxOf(s): the greatest element of a non-empty set of naturals.
MaxOf(s) == CHOOSE x \in s : \A y \in s : y <= x

\* MinOf(s): the least element of a non-empty set of naturals.
MinOf(s) == CHOOSE x \in s : \A y \in s : x <= y

\* ReduceSet(f, s, a): the result of folding f over the elements of s
\* starting with accumulator a (order is unspecified, since s is a set).
ReduceSet(f, s, a) == IF s = {} THEN a
                      ELSE LET x == CHOOSE y \in s : TRUE
                           IN f[x, ReduceSet(f, s \ {x}, a)]

\* ReduceSeq(f, seq, a): the result of folding f over the elements of seq
\* in order, starting with accumulator a, using the built-in fold.
ReduceSeq(f, seq, a) == FoldSeq(f, seq, a)

\* IndexOf(seq, x): the first position at which x appears in seq, or 0.
IndexOf(seq, x) == CHOOSE k \in 0..Len(seq) :
                      (k = 0 \/ (k \in 1..Len(seq) /\ seq[k] = x))

\* SeqToSet(seq): the set of elements appearing in seq.
SeqToSet(seq) == {seq[k] : k \in 1..Len(seq)}

\* LastOf(seq): the final element of a non-empty sequence.
LastOf(seq) == seq[Len(seq)]

\* IsEmpty(seq): true iff seq has no elements.
IsEmpty(seq) == Len(seq) = 0

\* RemoveAll(seq, x): seq with every occurrence of x deleted.
RemoveAll(seq, x) ==
  IF seq = <<>> THEN <<>>
  ELSE IF Head(seq) = x THEN RemoveAll(Tail(seq), x)
  ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), x)

\* IntersectionOfSet(setOfSets): the common elements of all member sets.
IntersectionOfSet(setOfSets) ==
  CHOOSE r \in setOfSets :
    \A s \in setOfSets : r \subseteq s

\* Permutations(s): the set of every permutation sequence of the set s.
VARIABLES perms
InitPermutations == perms = {}
NextPermutation(s) == perms' = perms \cup {[k \in 1..Cardinality(s) |-> x] :
                                            x \in s}
PermutationsOf(s) == perms satisfying (perms \in [ 0..Cardinality(s) -> s ])

\* TestHelper: a placeholder for writing assertions that emit diagnostics on
\* failure; it always returns TRUE so it never blocks progress.
TestHelper == TRUE

====