---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ------------------------------------------------------------
\* 1. Set intersection test (whether two sets overlap)
\* ------------------------------------------------------------
SetOverlap(S, T) == S \cap T # {}

\* ------------------------------------------------------------
\* 2. Maximum and minimum element selection from a set
\* ------------------------------------------------------------
SetMax(S) ==
  /\ S # {}
  /\ CHOOSE x \in S : \A y \in S : y <= x

SetMin(S) ==
  /\ S # {}
  /\ CHOOSE x \in S : \A y \in S : x <= y

\* ------------------------------------------------------------
\* 3. Generalized set reduction (fold over a set with an accumulator)
\* ------------------------------------------------------------
SetFold(S, a, f(_,_)) ==
  IF S = {} THEN a
  ELSE
    LET x == CHOOSE e \in S : TRUE
    IN SetFold(S \ {x}, f(a, x), f)

\* ------------------------------------------------------------
\* 4. Sequence reduction (fold over a sequence with an accumulator)
\* ------------------------------------------------------------
SeqFold(seq, a, f(_,_)) ==
  IF Len(seq) = 0 THEN a
  ELSE
    SeqFold(SubSeq(seq, 2, Len(seq)), f(a, seq[1]), f)

\* ------------------------------------------------------------
\* 5. Finding the index of an element in a sequence
\* ------------------------------------------------------------
SeqIndex(seq, elem) ==
  IF elem \in SeqToSet(seq) THEN
    CHOOSE i \in 1..Len(seq) : seq[i] = elem
  ELSE
    0

\* ------------------------------------------------------------
\* 6. Converting a sequence to the set of its elements
\* ------------------------------------------------------------
SeqToSet(seq) == { seq[i] : i \in DOMAIN seq }

\* ------------------------------------------------------------
\* 7. Getting the last element of a sequence
\* ------------------------------------------------------------
SeqLast(seq) ==
  /\ Len(seq) > 0
  /\ seq[Len(seq)]

\* ------------------------------------------------------------
\* 8. Testing if a sequence is empty
\* ------------------------------------------------------------
SeqIsEmpty(seq) == Len(seq) = 0

\* ------------------------------------------------------------
\* 9. Removing all occurrences of an element from a sequence
\* ------------------------------------------------------------
SeqRemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF seq[1] = elem
          THEN SeqRemoveAll(SubSeq(seq, 2, Len(seq)), elem)
          ELSE <<seq[1]>> \o SeqRemoveAll(SubSeq(seq, 2, Len(seq)), elem)

\* ------------------------------------------------------------
\* 10. Computing the intersection of a set of sets
\* ------------------------------------------------------------
SetOfSetsIntersection(SS) ==
  IF SS = {} THEN {}
  ELSE \bigcap SS

\* ------------------------------------------------------------
\* 11. Generating all permutation sequences of a finite set
\* ------------------------------------------------------------
Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE
    UNION {
      <<e>> \o p :
        e \in S,
        p \in Permutations(S \ {e})
    }

\* ------------------------------------------------------------
\* 12. Test helper for writing assertions that print diagnostic information on failure
\* ------------------------------------------------------------
Assert(cond, msg) ==
  IF cond THEN TRUE ELSE Print(msg) /\ FALSE

====