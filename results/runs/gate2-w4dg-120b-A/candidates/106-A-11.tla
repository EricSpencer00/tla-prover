---- MODULE Util ----
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
  MaxValue, MinValue

VARIABLES
  dummy

vars == <<dummy>>

\* A no-op spec: this library module has nothing to model, so the spec does
\* nothing at all.  All the action/temporal operators below are still
\* defined because the reference .cfg file lists them.
INIT == dummy = 0

NextStep == dummy' = dummy

Next == NextStep

Invariants == TRUE

Properties == TRUE

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ dummy \in 0..1
  /\ MaxValue \in -9..9
  /\ MinValue \in -9..9

\* 1) Set intersection test: true iff the two sets share at least one element.
Intersect(A, B) == \E x \in A : x \in B

\* 2) Maximum element selection from a set.
Maximum(A) == CHOOSE x \in A : \A y \in A : y <= x

\* 2) Minimum element selection from a set.
Minimum(A) == CHOOSE x \in A : \A y \in A : y >= x

\* 3) Generalized set reduction (fold over a set with an accumulator).
SetReduce(f, init, S) ==
  LET fold[T \in SUBSET S] ==
        IF T = {} THEN init
        ELSE LET x == CHOOSE y \in T : TRUE
                 rest == fold[T \ {x}]
              IN f[x, rest]
  IN fold[S]

\* 4) Sequence reduction (fold over a sequence with an accumulator), via a library operator.
SeqReduce(f, init, s) == ReduceSeq(f, init, s)

\* 5) Find the index of an element in a sequence.
IndexOf(s, x) == CHOOSE k \in 1..Len(s) : s[k] = x

\* 6) Convert a sequence to the set of its elements.
SeqToSet(s) == {s[i] : i \in 1..Len(s)}

\* 7) Get the last element of a non-empty sequence.
Last(s) == s[Len(s)]

\* 8) Test if a sequence is empty.
EmptySeq(s) == Len(s) = 0

\* 9) Remove all occurrences of an element from a sequence.
RemoveAll(s, x) ==
  IF s = <<>> THEN <<>>
  ELSE IF Head(s) = x THEN RemoveAll(Tail(s), x)
  ELSE <<Head(s)>> \o RemoveAll(Tail(s), x)

\* 10) Intersection of a set of sets.
SetIntersection(X) == {x \in UNION X : \A S \in X : x \in S}

\* 11) Generate all permutation sequences of a finite set.
Permutations(S) ==
  IF S = {} THEN {<<>>}
  ELSE {<<x>> \o p : x \in S, p \in Permutations(S \ {x})}

\* 12) Test helper that prints diagnostics on failure.
TestHelper(b) == IF b THEN TRUE ELSE Print("FAILED")

====