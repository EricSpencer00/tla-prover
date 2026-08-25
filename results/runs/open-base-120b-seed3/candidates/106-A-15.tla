---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(* Utility operators                                                       *)
(***************************************************************************)

\* 1. Set intersection test (whether two sets overlap)
SetOverlap(S, T) == S \cap T # {}

\* 2. Maximum element selection from a set
SetMax(S) ==
  IF S = {} THEN
    NULL
  ELSE
    LET m == CHOOSE x \in S : \A y \in S : y <= x
    IN m

\* 3. Minimum element selection from a set
SetMin(S) ==
  IF S = {} THEN
    NULL
  ELSE
    LET m == CHOOSE x \in S : \A y \in S : x <= y
    IN m

\* 4. Generalized set reduction (fold over a set with an accumulator)
SetReduce(S, f(_,_), a) ==
  IF S = {} THEN
    a
  ELSE
    LET x == CHOOSE y \in S
    IN SetReduce(S \ {x}, f, f(a, x))

\* 5. Sequence reduction (fold over a sequence with an accumulator)
SeqReduce(seq, f(_,_), a) ==
  IF Len(seq) = 0 THEN
    a
  ELSE
    SeqReduce(Tail(seq), f, f(a, Head(seq)))

\* 6. Finding the index of an element in a sequence (1‑based; 0 if absent)
SeqIndex(seq, elem) ==
  IF elem \notin set(seq) THEN
    0
  ELSE
    CHOOSE i \in 1..Len(seq) : seq[i] = elem

\* 7. Converting a sequence to the set of its elements
SeqToSet(seq) == set(seq)

\* 8. Getting the last element of a sequence
SeqLast(seq) ==
  IF Len(seq) = 0 THEN
    NULL
  ELSE
    seq[Len(seq)]

\* 9. Testing if a sequence is empty
SeqIsEmpty(seq) == Len(seq) = 0

\* 10. Removing all occurrences of an element from a sequence
SeqRemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN
    <<>>
  ELSE IF Head(seq) = elem THEN
    SeqRemoveAll(Tail(seq), elem)
  ELSE
    <<Head(seq)>> \o SeqRemoveAll(Tail(seq), elem)

\* 11. Intersection of a set of sets
SetIntersection(SS) == INTERSECTION(SS)

\* 12. Generating all permutation sequences of a finite set
Permutations(S) ==
  IF S = {} THEN
    {<<>>}
  ELSE
    { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

\* 13. Test helper for assertions with diagnostic output
TestHelper(expr, msg) ==
  IF expr THEN
    TRUE
  ELSE
    /\ Print(msg)
    /\ FALSE

(***************************************************************************)
(* Stubs required by the reference configuration                           *)
(***************************************************************************)

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

=============================================================================