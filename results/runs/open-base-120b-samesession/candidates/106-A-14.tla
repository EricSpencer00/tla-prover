---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

(*-----------------------------------------------------------------
  Utility operators for set and sequence manipulation.
 -----------------------------------------------------------------*)

\* 1. Set intersection test (whether two sets overlap)
SetOverlap(A, B) == ∃ x \in A : x \in B

\* 2. Maximum element of a set (returns NULL if the set is empty)
SetMax(S) ==
  IF S = {} THEN NULL
  ELSE CHOOSE x \in S : ∀ y \in S : y <= x

\* 3. Minimum element of a set (returns NULL if the set is empty)
SetMin(S) ==
  IF S = {} THEN NULL
  ELSE CHOOSE x \in S : ∀ y \in S : x <= y

\* 4. Generalized set reduction (fold over a set with an accumulator)
RECURSIVE SetFold
SetFold(S, acc, f) ==
  IF S = {} THEN acc
  ELSE
    LET e == CHOOSE x \in S : TRUE
    IN SetFold(S \ {e}, f(acc, e), f)

\* 5. Sequence reduction (fold over a sequence with an accumulator)
RECURSIVE SeqFold
SeqFold(seq, acc, f) ==
  IF Len(seq) = 0 THEN acc
  ELSE SeqFold(Tail(seq), f(acc, Head(seq)), f)

\* 6. Finding the index of an element in a sequence (returns -1 if absent)
SeqIndex(seq, elem) ==
  IF ∃ i \in 1 .. Len(seq) : seq[i] = elem
    THEN CHOOSE i \in 1 .. Len(seq) : seq[i] = elem
    ELSE -1

\* 7. Converting a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in 1 .. Len(seq) }

\* 8. Getting the last element of a sequence (NULL if empty)
SeqLast(seq) ==
  IF Len(seq) = 0 THEN NULL
  ELSE seq[Len(seq)]

\* 9. Testing if a sequence is empty
SeqIsEmpty(seq) == Len(seq) = 0

\* 10. Removing all occurrences of an element from a sequence
RECURSIVE SeqRemoveAll
SeqRemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF Head(seq) = elem
        THEN SeqRemoveAll(Tail(seq), elem)
        ELSE <<Head(seq)>> \o SeqRemoveAll(Tail(seq), elem)

\* 11. Computing the intersection of a set of sets
SetIntersection(setOfSets) == INTERSECTION(setOfSets)

\* 12. Generating all permutation sequences of a finite set
RECURSIVE Permutations
Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

\* 13. Test helper for writing assertions that print diagnostics on failure
TestHelper(expr, msg) ==
  IF expr THEN TRUE
  ELSE (Print(msg); FALSE)

(*-----------------------------------------------------------------
  Stubs required by the configuration (no state in this library)
 -----------------------------------------------------------------*)
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====