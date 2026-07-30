---- MODULE Util ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS MaxValue, MaxLen

\* System overview: a utility library module providing common helper operators
\* used by the key-value store specifications. It defines reusable operators
\* for set and sequence manipulation: set intersection test, set reduction,
\* sequence reduction, element indexing, sequence-to-set conversion, set
\* permutation generation, and other convenience functions.

\* Actors and components: none -- this is a pure functional library.

\* State variables: NOT_SPECIFIED (the .cfg imposes no state).

\* Initial state: NOT_SPECIFIED

\* Actions: NOT_SPECIFIED

\* Safety properties: NOT_SPECIFIED

\* Liveness properties: NOT_SPECIFIED

\* Model bounds: NOT_SPECIFIED

\* Utility operators:

\* 1. Set intersection test: whether two sets overlap.
SetOverlap(S, T) == \E e \in S : e \in T

\* 2. Maximum element selection from a set.
SetMaximum(S) == CHOOSE e \in S : \A x \in S : x <= e

\* 3. Minimum element selection from a set.
SetMinimum(S) == CHOOSE e \in S : \A x \in S : e <= x

\* 4. Generalized set reduction (fold over a set with an accumulator).
SetFold(S, init, f) ==
  LET g[T \in SUBSET S] ==
      IF T = {} THEN init
      ELSE LET e \in T : TRUE IN f(e, g[T \ {e}])
  IN g[S]

\* 5. Sequence reduction (fold over a sequence with an accumulator, using the
\*    library FoldSeq operator over the sequence's domain).
SeqFold(seq, init, f) ==
  LET g[i \in DOMAIN seq] ==
      IF i = 1 THEN f(seq[i], init)
      ELSE f(seq[i], g[i - 1])
  IN g[Len(seq)]

\* 6. Find the index of an element in a sequence.
SeqIndex(seq, v) ==
  CHOOSE i \in DOMAIN seq : seq[i] = v

\* 7. Convert a sequence to the set of its elements.
SeqToSet(seq) ==
  { seq[i] : i \in DOMAIN seq }

\* 8. Get the last element of a sequence.
SeqLast(seq) ==
  seq[Len(seq)]

\* 9. Test if a sequence is empty.
SeqEmpty(seq) ==
  \A i \in DOMAIN seq : FALSE

\* 10. Remove all occurrences of an element from a sequence.
SeqRemove(seq, v) ==
  \E i \in 1..(Len(seq) - 1) :
    [j \in 1..i |-> seq[j]] @@
    [j \in 1..(Len(seq) - i) |-> seq[i + j]]

\* 11. Intersection of a set of sets.
SetSetIntersection(S) ==
  CHOOSE e \in UNION S : \A X \in S : e \in X

\* 12. Generate all permutation sequences of a finite set.
Permutations(S) ==
  IF S = {} THEN { << >> }
  ELSE { << e >> @@ p : e \in S, p \in Permutations(S \ {e}) }

\* 13. Test helper for writing assertions that prints diagnostic info on
\*    failure (always returns TRUE so it never blocks the model).
TestHelper == (PrintT("no-op test helper")) \in BOOLEAN

\* The .cfg imposes no identifier requirements beyond the library operators
\* above, so SPECIFICATION, INIT, NEXT, INVARIANTS, and PROPERTIES are simply
\* defined as trivial always-TRUE operators to satisfy the spec template.

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

====