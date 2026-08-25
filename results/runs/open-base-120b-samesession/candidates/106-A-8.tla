---- MODULE Util ----
EXTEND Naturals, Sequences, FiniteSets, TLC

(* --------------------------------------------------------------------
   Utility operators
   -------------------------------------------------------------------- *)

\* 1. Set intersection test (whether two sets overlap)
Overlaps(S, T) == (S \cap T) # {}

\* 2. Maximum element selection from a set
Max(S) ==
  IF S = {} THEN {}
  ELSE CHOOSE x \in S: \A y \in S: y <= x

\* 3. Minimum element selection from a set
Min(S) ==
  IF S = {} THEN {}
  ELSE CHOOSE x \in S: \A y \in S: x <= y

\* 4. Generalized set reduction (fold over a set with an accumulator)
SetReduce(F, a, S) ==
  IF S = {} THEN a
  ELSE
    LET e == CHOOSE x \in S: TRUE
        Rest == S \ {e}
    IN SetReduce(F, F(a, e), Rest)

\* 5. Sequence reduction (fold over a sequence with an accumulator)
SeqReduce(F, a, s) == FoldSeq(F, a, s)

\* 6. Finding the index of an element in a sequence (1‑based, 0 if absent)
IndexHelper(s, e, i) ==
  IF i > Len(s) THEN 0
  ELSE IF s[i] = e THEN i
  ELSE IndexHelper(s, e, i + 1)

SeqIndex(s, e) == IndexHelper(s, e, 1)

\* 7. Converting a sequence to the set of its elements
SeqToSet(s) == { s[i] : i \in 1..Len(s) }

\* 8. Getting the last element of a sequence
Last(s) == IF Len(s) = 0 THEN {} ELSE s[Len(s)]

\* 9. Testing if a sequence is empty
IsEmpty(s) == Len(s) = 0

\* 10. Removing all occurrences of an element from a sequence
RemoveAll(s, e) ==
  IF Len(s) = 0 THEN <<>>
  ELSE IF s[1] = e THEN RemoveAll(SubSeq(s, 2, Len(s)), e)
  ELSE << s[1] >> \o RemoveAll(SubSeq(s, 2, Len(s)), e)

\* 11. Computing the intersection of a set of sets
SetIntersection(S) == INTERSECTION S

\* 12. Generating all permutation sequences of a finite set
Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

\* 13. Test helper for writing assertions that print diagnostic information
TestHelper(expr, msg) == Assert(expr, msg)

(* --------------------------------------------------------------------
   Place‑holder specifications for completeness (no concrete behavior)
   -------------------------------------------------------------------- *)

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====