---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS MaxVal, MaxPerm

\* Set intersection: true iff the two sets overlap.
Intersects(A, B) == \E x \in A : x \in B

\* Maximum element of a nonempty set.
MaxOf(S) == CHOOSE m \in S : \A x \in S : x <= m

\* Minimum element of a nonempty set.
MinOf(S) == CHOOSE m \in S : \A x \in S : m <= x

\* Generalized set reduction (fold) with an accumulator.
ReduceSet(f, S, init) == LET
  g[T \in SUBSET S] ==
    IF T = {} THEN init
    ELSE \E x \in T : g[T \ {x}] = f(x, g[T \ {x}])
  IN g[S]

\* Sequence reduction (fold) using the library operator.
ReduceSeq(f, s, init) == FoldSeq(f, s, init)

\* Index of an element in a sequence, or -1 if absent.
IndexOf(e, s) == LET
  f[i \in 1..Len(s)] == IF s[i] = e THEN i ELSE -1
  IN SelectSeq(f, Len(s), -1)

\* Convert a sequence to the set of its elements.
SeqToSet(s) == { s[i] : i \in 1..Len(s) }

\* Last element of a nonempty sequence.
LastOf(s) == s[Len(s)]

\* Empty-sequence test.
Empty(s) == Len(s) = 0

\* Remove all occurrences of an element from a sequence.
RemoveAll(e, s) == SelectSeq(LAMBDA x \in DOMAIN s : IF s[x] = e THEN -1 ELSE x, Len(s), -1)

\* Intersection of a set of sets.
IntersectAll(T) == ReduceSet(Intersects, T, TRUE)

\* Generate all permutation sequences of a finite set.
Permutations(S) ==
  LET
    f[T \in SUBSET S] ==
      IF T = {} THEN { << >> }
      ELSE { << x >> ^ p : x \in T, p \in f[T \ {x}] }
  IN f[S]

\* A test helper: asserts a condition and prints a diagnostic on failure.
Assert(cond, msg) == IF cond THEN TRUE ELSE PrintTLA(msg) /\ FALSE

\* The following identifiers are defined with no-body default implementation,
\* because the .cfg file does not require any; they must exist nonetheless.
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == BOOLEAN
PROPERTIES == BOOLEAN

====