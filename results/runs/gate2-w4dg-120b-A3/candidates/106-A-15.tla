---- MODULE Util ----
EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS EmptySeq, MaxInt

ASSUME EmptySeq = << >> /\ MaxInt \in Nat

SpecVersion == "Util with full utility suite"

\* Utility operator: set intersection test (whether two sets overlap).
Intersects(S, T) == \E x \in S : x \in T

\* Utility operator: maximum element selection from a set.
MaxOf(S) ==
  LET m == CHOOSE x \in S : \A y \in S : y <= x
  IN m

\* Utility operator: minimum element selection from a set.
MinOf(S) ==
  LET m == CHOOSE x \in S : \A y \in S : y >= x
  IN m

\* Utility operator: generalized set reduction (fold over a set with an accumulator).
\* The operation must be commutative so the order of folding over a set is irrelevant.
FoldSet(S, base, op) ==
  LET FoldEnum(E, a) ==
        IF E = {} THEN a
        ELSE
          LET x == CHOOSE y \in E : TRUE
          IN FoldEnum(E \ {x}, op(a, x))
  IN FoldEnum(S, base)

\* Utility operator: sequence reduction (fold over a sequence with an accumulator).
FoldSeq(seq, base, op) == FoldSeq(seq, base, op)

\* Utility operator: find the index of an element in a sequence.
IndexOf(seq, elem) ==
  IF \E k \in 1..Len(seq) : seq[k] = elem
  THEN CHOOSE k \in 1..Len(seq) : seq[k] = elem
  ELSE 0

\* Utility operator: convert a sequence to the set of its elements.
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* Utility operator: get the last element of a sequence.
LastOf(seq) == IF seq = EmptySeq THEN MaxInt ELSE seq[Len(seq)]

\* Utility operator: test if a sequence is empty.
IsEmpty(seq) == seq = EmptySeq

\* Utility operator: remove all occurrences of an element from a sequence.
RemoveAll(seq, elem) ==
  SELECT s \in SUBSET (SeqToSet(seq)) : s = (SeqToSet(seq) \ {elem})

\* Utility operator: intersection of a set of sets.
IntersectSets(S) == FoldSet(S, {}, Intersects)

\* Utility operator: generate all permutation sequences of a finite set.
\* Permutations are infinite in number for infinite sets, so this is only
\* defined for finite sets.
Permutations(S) ==
  IF S = {} THEN {EmptySeq}
  ELSE
    \E x \in S :
      \E rest \in Permutations(S \ {x}) :
        { <<x>> \o rest }

\* Test helper: write an assertion that prints diagnostics on failure.
\* The operator always returns TRUE, so it can be used inside an
\* ASSUME or a property without affecting correctness; it prints its
\* arguments to the TLC trace on evaluation.
AssertArgs(a, b) ==
  LET print == [a |-> a, b |-> b]
  IN print \in print

\* The specification is a single-state placeholder; there are no actions.
Spec == TRUE

Init == TRUE

Next == TRUE

SpecOK == Spec /\ Init /\ Next

====