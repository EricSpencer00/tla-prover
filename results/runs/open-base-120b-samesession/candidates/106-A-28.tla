---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\*  Utility operators
\* ----------------------------------------------------------------------

\* 1. Set overlap test (whether two sets intersect)
SetOverlap(S, T) == \E x \in S : x \in T

\* 2. Maximum element of a non‑empty set (assumes a total order)
SetMax(S) ==
  CHOOSE x \in S :
    \A y \in S : y <= x

\* 3. Minimum element of a non‑empty set (assumes a total order)
SetMin(S) ==
  CHOOSE x \in S :
    \A y \in S : x <= y

\* 4. Generalized set reduction (fold over a set with an accumulator)
SetFoldRec(S, acc, f) ==
  IF S = {} THEN acc
  ELSE
    LET x == CHOOSE y \in S IN
      SetFoldRec(S \ {x}, f(acc, x), f)

SetFold(S, acc0, f) == SetFoldRec(S, acc0, f)

\* 5. Sequence reduction (fold over a sequence with an accumulator)
SeqFold(seq, acc0, f) ==
  IF Len(seq) = 0 THEN acc0
  ELSE SeqFold(Tail(seq), f(acc0, Head(seq)), f)

\* 6. Index of an element in a sequence (1‑based, 0 if not present)
IndexOf(seq, elem) ==
  IF Len(seq) = 0 THEN 0
  ELSE IF Head(seq) = elem THEN 1
       ELSE
         LET i == IndexOf(Tail(seq), elem) IN
           IF i = 0 THEN 0 ELSE i + 1

\* 7. Convert a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in 1 .. Len(seq) }

\* 8. Last element of a sequence (NULL if empty)
Last(seq) ==
  IF Len(seq) = 0 THEN NULL
  ELSE seq[Len(seq)]

\* 9. Test if a sequence is empty
IsSeqEmpty(seq) == Len(seq) = 0

\* 10. Remove all occurrences of an element from a sequence
RemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF Head(seq) = elem THEN RemoveAll(Tail(seq), elem)
       ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), elem)

\* 11. Intersection of a set of sets
SetIntersection(SS) == INTERSECTION SS

\* 12. Generate all permutations of a finite set
Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE
    UNION { <<x>> \o p :
              x \in S,
              p \in Permutations(S \ {x}) }

\* 13. Test helper that prints a message on failure
AssertHelper(cond, msg) ==
  IF cond THEN TRUE ELSE Print(msg) /\ FALSE

\* ----------------------------------------------------------------------
\*  Trivial specification scaffolding required by the task
\* ----------------------------------------------------------------------
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

====