---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* 1. Set intersection test (whether two sets overlap)
SetOverlap(S, T) == \E x \in S: x \in T

\* 2. Maximum element selection from a set (returns NULL if the set is empty)
SetMax(S) ==
  IF S = {} THEN NULL
  ELSE CHOOSE x \in S: \A y \in S: y <= x

\* 2. Minimum element selection from a set (returns NULL if the set is empty)
SetMin(S) ==
  IF S = {} THEN NULL
  ELSE CHOOSE x \in S: \A y \in S: y >= x

\* 3. Generalized set reduction (fold over a set with an accumulator)
\*    f is a binary operator: f(acc, element) -> newAcc
ReduceSet(S, acc, f) ==
  IF S = {} THEN acc
  ELSE
    LET x == CHOOSE e \in S: TRUE
    IN ReduceSet(S \ {x}, f(acc, x), f)

\* 4. Sequence reduction (fold over a sequence with an accumulator)
\*    f is a binary operator: f(acc, element) -> newAcc
ReduceSeq(seq, acc, f) ==
  IF Len(seq) = 0 THEN acc
  ELSE ReduceSeq(Tail(seq), f(acc, Head(seq)), f)

\* 5. Finding the index of an element in a sequence (1‑based, 0 if not found)
IndexOf(seq, elem) ==
  IF Len(seq) = 0 THEN 0
  ELSE IF Head(seq) = elem THEN 1
  ELSE
    LET rest == IndexOf(Tail(seq), elem) IN
      IF rest = 0 THEN 0 ELSE 1 + rest

\* 6. Converting a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in DOMAIN seq }

\* 7. Getting the last element of a sequence (NULL if empty)
Last(seq) ==
  IF Len(seq) = 0 THEN NULL
  ELSE seq[Len(seq)]

\* 8. Testing if a sequence is empty
IsEmpty(seq) == Len(seq) = 0

\* 9. Removing all occurrences of an element from a sequence
RemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF Head(seq) = elem
       THEN RemoveAll(Tail(seq), elem)
       ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), elem)

\* 10. Computing the intersection of a set of sets
IntersectSets(S) == INTERSECTION S

\* 11. Generating all permutation sequences of a finite set
Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

\* 12. Test helper for assertions that prints diagnostic information on failure
Assert(pred, msg) ==
  IF pred THEN TRUE
  ELSE Print(msg) /\ FALSE

====