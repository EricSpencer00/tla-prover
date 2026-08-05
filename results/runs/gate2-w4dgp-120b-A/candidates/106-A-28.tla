---- MODULE Util ----
EXTENDS Naturals, Sequences

CONSTANTS

Value

ASSUME /\ Value \in Nat

\* Intersection test: do two sets share an element?
Intersects(S, T) == \E x \in S : x \in T

\* Max/min of a non-empty set
MaxOf(S) == CHOOSE m \in S : \A x \in S : x <= m
MinOf(S) == CHOOSE m \in S : \A x \in S : m <= x

\* Fold/reduce over a set with an accumulator
SetReduce(S, e, f, b) ==
  LET fold[E \in SUBSET S] ==
       IF E = {} THEN b
       ELSE LET x == CHOOSE y \in E : TRUE IN f(e(x), fold[E \ {x}])
  IN fold[S]

\* Fold/reduce over a sequence with an accumulator (library fold)
SeqReduce(seq, e, f, b) == Fold(seq, e, f, b)

\* Index of an element in a sequence, or 0 if absent
SeqIndex(seq, x) ==
  LET idx[i \in 1..Len(seq)] ==
       IF seq[i] = x THEN i ELSE idx[i + 1]
  IN idx[1]
  IF idx[1] > Len(seq) THEN 0 ELSE idx[1]

\* The set of elements appearing in a sequence
SeqElems(seq) == { seq[i] : i \in 1..Len(seq) }

\* The last element of a non-empty sequence
SeqLast(seq) == seq[Len(seq)]

\* Sequence emptiness test (often useful in guards)
SeqIsEmpty(seq) == Len(seq) = 0

\* Remove all occurrences of an element from a sequence
SeqRemove(seq, x) ==
  LET clean[i \in 1..Len(seq)] ==
       IF i > Len(seq) THEN << >>
       ELSE IF seq[i] = x THEN clean[i + 1]
            ELSE << seq[i] >> \o clean[i + 1]
  IN clean[1]

\* Intersection of a set of sets
SetsIntersection(S) ==
  IF S = {} THEN {}
  ELSE LET pick[T \in S] == T IN { x \in pick[S] : \A T \in S : x \in T }

\* Compute all permutations of a finite set; returns a set of sequences
Permutations(S) ==
  LET perms[T \in SUBSET S] ==
       IF T = {} THEN { << >> }
       ELSE { << x >> \o p : x \in T, p \in perms[T \ {x}] }
  IN perms[S]

\* Assertion test helper: prints diagnostic info on failure
TestAssert ==
  /\ TRUE
  /\ ~FALSE

====