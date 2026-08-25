---- MODULE Util ----
EXTENDS Naturals, Sequences, TLC

\* ------------------------------------------------------------
\* 1. Set intersection test (whether two sets overlap)
\* ------------------------------------------------------------
SetOverlap(S, T) == \E x \in S : x \in T

\* ------------------------------------------------------------
\* 2. Maximum and minimum element selection from a set
\*    (assumes the elements are comparable, e.g., numbers)
\* ------------------------------------------------------------
SetMax(S) == CHOOSE x \in S : \A y \in S : y <= x
SetMin(S) == CHOOSE x \in S : \A y \in S : x <= y

\* ------------------------------------------------------------
\* 3. Generalized set reduction (fold over a set with an accumulator)
\* ------------------------------------------------------------
SetFold(S, op, a) ==
  IF S = {} THEN a
  ELSE
    LET e == CHOOSE x \in S : TRUE
    IN SetFold(S \ {e}, op, op(a, e))

\* ------------------------------------------------------------
\* 4. Sequence reduction (fold over a sequence with an accumulator)
\*    implemented via the library FoldSeq operator
\* ------------------------------------------------------------
SeqFold(seq, op, a) == FoldSeq(seq, op, a)

\* ------------------------------------------------------------
\* 5. Finding the index of an element in a sequence
\*    (1‑based index; returns 0 if the element is not present)
\* ------------------------------------------------------------
IndexOf(seq, e) ==
  IF \E i \in 1..Len(seq) : seq[i] = e
  THEN CHOOSE i \in 1..Len(seq) : seq[i] = e
  ELSE 0

\* ------------------------------------------------------------
\* 6. Converting a sequence to the set of its elements
\* ------------------------------------------------------------
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* ------------------------------------------------------------
\* 7. Getting the last element of a sequence
\* ------------------------------------------------------------
SeqLast(seq) == seq[Len(seq)]

\* ------------------------------------------------------------
\* 8. Testing if a sequence is empty
\* ------------------------------------------------------------
SeqIsEmpty(seq) == Len(seq) = 0

\* ------------------------------------------------------------
\* 9. Removing all occurrences of an element from a sequence
\* ------------------------------------------------------------
RemoveAll(seq, e) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF seq[1] = e THEN RemoveAll(Tail(seq), e)
       ELSE << seq[1] >> \o RemoveAll(Tail(seq), e)

\* ------------------------------------------------------------
\* 10. Computing the intersection of a set of sets
\* ------------------------------------------------------------
IntersectAll(SS) == INTERSECTION SS

\* ------------------------------------------------------------
\* 11. Generating all permutation sequences of a finite set
\* ------------------------------------------------------------
Permutations(S) ==
  IF S = {} THEN { << >> }
  ELSE UNION { << e >> \o p : e \in S, p \in Permutations(S \ {e}) }

\* ------------------------------------------------------------
\* 12. Test helper for writing assertions that print diagnostics on failure
\* ------------------------------------------------------------
AssertHelper(cond, msg) ==
  IF cond THEN TRUE
  ELSE Print(msg) /\ FALSE

\* ------------------------------------------------------------
\* Trivial specification identifiers required by the task
\* ------------------------------------------------------------
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====