---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\* Trivial specification (required identifiers)
\* ----------------------------------------------------------------------
VARIABLES dummy

Init == dummy = FALSE

Next == UNCHANGED dummy

SPECIFICATION == Init /\ [][Next]_<<dummy>>

INVARIANTS == TRUE

PROPERTIES == TRUE

\* ----------------------------------------------------------------------
\* Utility operators
\* ----------------------------------------------------------------------

\* 1. Set intersection test (whether two sets overlap)
SetOverlap(S, T) == (S \cap T) # {}

\* 2. Maximum element selection from a set
\*    Returns a distinguished value NULL when the set is empty.
CONSTANT NULL
SetMax(S) ==
  IF S = {} THEN NULL
  ELSE CHOOSE x \in S : \A y \in S : x >= y

\* 3. Minimum element selection from a set
SetMin(S) ==
  IF S = {} THEN NULL
  ELSE CHOOSE x \in S : \A y \in S : x <= y

\* 4. Generalized set reduction (fold over a set with an accumulator)
\*    f is a binary operator: f(element, accumulator) -> newAccumulator
SetFold(S, init, f) ==
  LET Rec(T) ==
    IF T = {} THEN init
    ELSE
      LET e == CHOOSE x \in T
      IN f(e, Rec(T \ {e}))
  IN Rec(S)

\* 5. Sequence reduction (fold over a sequence with an accumulator)
\*    f is a binary operator: f(element, accumulator) -> newAccumulator
SeqFold(seq, init, f) ==
  IF Len(seq) = 0 THEN init
  ELSE f(seq[1], SeqFold(Tail(seq), init, f))

\* 6. Finding the index of an element in a sequence (1‑based, 0 if not found)
SeqIndex(seq, elem) ==
  IF Len(seq) = 0 THEN 0
  ELSE IF seq[1] = elem THEN 1
  ELSE
    LET idx == SeqIndex(Tail(seq), elem)
    IN IF idx = 0 THEN 0 ELSE idx + 1

\* 7. Converting a sequence to the set of its elements
SeqToSet(seq) == { x : \E i \in 1..Len(seq) : seq[i] = x }

\* 8. Getting the last element of a sequence (NULL if empty)
SeqLast(seq) ==
  IF Len(seq) = 0 THEN NULL
  ELSE seq[Len(seq)]

\* 9. Testing if a sequence is empty
SeqIsEmpty(seq) == Len(seq) = 0

\* 10. Removing all occurrences of an element from a sequence
SeqRemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF seq[1] = elem THEN SeqRemoveAll(Tail(seq), elem)
  ELSE <<seq[1]>> \o SeqRemoveAll(Tail(seq), elem)

\* 11. Computing the intersection of a set of sets
SetIntersectionOfSetOfSets(SS) ==
  IF SS = {} THEN {}
  ELSE \cap SS

\* 12. Generating all permutation sequences of a finite set
Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

\* 13. Test helper for writing assertions that print diagnostic information on failure
\*     (In TLA+ we cannot print, so this is a no‑op that simply returns the condition.)
TestHelper(cond, msg) == cond

====