---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\*  Utility operators
\* ----------------------------------------------------------------------

\* 1. Set overlap (whether two sets intersect)
SetOverlap(S, T) == \E x \in S : x \in T

\* 2. Maximum element of a non‑empty set (uses total ordering on elements)
SetMax(S) == 
  CHOOSE x \in S : \A y \in S : y <= x

\* 3. Minimum element of a non‑empty set
SetMin(S) == 
  CHOOSE x \in S : \A y \in S : x <= y

\* 4. Generalized set reduction (fold over a set with an accumulator)
\*    f is a binary operator: f(acc, elem)
SetReduce(S, init, f(_,_)) == 
  IF S = {} THEN init
  ELSE 
    LET e == CHOOSE x \in S : TRUE IN
      SetReduce(S \ {e}, f(init, e), f)

\* 5. Sequence reduction (fold over a sequence with an accumulator)
\*    f is a binary operator: f(acc, elem)
SeqReduce(seq, init, f(_,_)) == 
  IF Len(seq) = 0 THEN init
  ELSE 
    SeqReduce(SubSeq(seq, 2, Len(seq)), f(init, seq[1]), f)

\* 6. Index of the first occurrence of an element in a sequence (0 if absent)
SeqIndex(seq, elem) == 
  IF \E i \in 1..Len(seq) : seq[i] = elem
  THEN Min({ i \in 1..Len(seq) : seq[i] = elem })
  ELSE 0

\* 7. Convert a sequence to the set of its elements
SeqToSet(seq) == { e : \E i \in 1..Len(seq) : seq[i] = e }

\* 8. Last element of a sequence (returns NULL for empty sequence)
Last(seq) == IF Len(seq) = 0 THEN NULL ELSE seq[Len(seq)]

\* 9. Test if a sequence is empty
IsEmpty(seq) == Len(seq) = 0

\* 10. Remove all occurrences of an element from a sequence
RemoveAll(seq, elem) == 
  IF Len(seq) = 0 THEN <<>>
  ELSE IF seq[1] = elem
       THEN RemoveAll(SubSeq(seq, 2, Len(seq)), elem)
       ELSE <<seq[1]>> \o RemoveAll(SubSeq(seq, 2, Len(seq)), elem)

\* 11. Intersection of a set of sets
SetIntersection(SS) == { x : \A S \in SS : x \in S }

\* 12. Generate all permutations of a finite set
Permutations(S) == 
  IF S = {} THEN { <<>> }
  ELSE UNION { <<e>> \o p : e \in S , p \in Permutations(S \ {e}) }

\* 13. Assertion helper that prints a message on failure
AssertHelper(pred, msg) == 
  IF pred THEN TRUE 
  ELSE (Print(msg); FALSE)

\* ----------------------------------------------------------------------
\*  Trivial specification skeleton (required identifiers)
\* ----------------------------------------------------------------------

INIT == TRUE

NEXT == TRUE

SPECIFICATION == INIT /\ [][NEXT]_<<>>

INVARIANTS == TRUE

PROPERTIES == TRUE

====