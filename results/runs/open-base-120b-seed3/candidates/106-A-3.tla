---- MODULE Util ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Utility operators
\* ----------------------------------------------------------------------

\* 1. Set intersection test (whether two sets overlap)
SetOverlap(S, T) == (S \cap T) # {}

\* 2. Maximum and minimum element selection from a set
SetMax(S) ==
  IF S = {} THEN NULL
  ELSE CHOOSE x \in S : \A y \in S : y <= x

SetMin(S) ==
  IF S = {} THEN NULL
  ELSE CHOOSE x \in S : \A y \in S : x <= y

\* 3. Generalized set reduction (fold over a set with an accumulator)
RECURSIVE SetFold(_,_ ,_)
SetFold(S, acc, op) ==
  IF S = {} THEN acc
  ELSE
    LET e == CHOOSE x \in S : TRUE
    IN SetFold(S \ {e}, op(acc, e), op)

\* 4. Sequence reduction (fold over a sequence with an accumulator)
RECURSIVE SeqFold(_,_ ,_)
SeqFold(seq, acc, op) ==
  IF Len(seq) = 0 THEN acc
  ELSE SeqFold(SeqTail(seq), op(acc, SeqHead(seq)), op)

\* 5. Finding the index of an element in a sequence (1‑based, 0 if absent)
SeqIndex(seq, elem) ==
  IF elem \in SeqToSet(seq) THEN
    CHOOSE i \in 1..Len(seq) : seq[i] = elem
  ELSE 0

\* 6. Converting a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* 7. Getting the last element of a sequence
SeqLast(seq) ==
  IF Len(seq) = 0 THEN NULL
  ELSE seq[Len(seq)]

\* 8. Testing if a sequence is empty
SeqIsEmpty(seq) == Len(seq) = 0

\* 9. Removing all occurrences of an element from a sequence
RECURSIVE SeqRemoveAll(_,_)
SeqRemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF SeqHead(seq) = elem
        THEN SeqRemoveAll(SeqTail(seq), elem)
        ELSE <<SeqHead(seq)>> \o SeqRemoveAll(SeqTail(seq), elem)

\* 10. Computing the intersection of a set of sets
SetIntersection(SS) ==
  { x \in UNION SS : \A S \in SS : x \in S }

\* 11. Generating all permutation sequences of a finite set
RECURSIVE Permutations(_)
Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

\* 12. Test helper for writing assertions that print diagnostic information
TestHelper(cond, msg) ==
  IF cond THEN TRUE
  ELSE (Print(msg) \/ FALSE)

\* ----------------------------------------------------------------------
\* Specification scaffolding (required identifiers)
\* ----------------------------------------------------------------------
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====