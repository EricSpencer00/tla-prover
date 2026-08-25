---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Utility operators
\* ----------------------------------------------------------------------

\* 1. Set intersection test (whether two sets overlap)
SetOverlap(S, T) == \E x \in S : x \in T

\* 2. Maximum element selection from a set (returns NULL for empty set)
SetMax(S) ==
  IF S = {} THEN NULL
  ELSE
    LET m == CHOOSE x \in S : \A y \in S : y <= x
    IN m

\* 2. Minimum element selection from a set (returns NULL for empty set)
SetMin(S) ==
  IF S = {} THEN NULL
  ELSE
    LET m == CHOOSE x \in S : \A y \in S : x <= y
    IN m

\* 3. Generalized set reduction (fold over a set with an accumulator)
\*    f is a binary operator: f(acc, element)
SetReduce(S, acc, f) ==
  IF S = {} THEN acc
  ELSE
    LET x == CHOOSE y \in S : TRUE
    IN SetReduce(S \ {x}, f(acc, x), f)

\* 4. Sequence reduction (fold over a sequence with an accumulator)
\*    Uses the same f as SetReduce
SeqReduce(seq, acc, f) ==
  IF Len(seq) = 0 THEN acc
  ELSE SeqReduce(Tail(seq), f(acc, Head(seq)), f)

\* 5. Finding the index of an element in a sequence
\*    Returns -1 if the element is not present
IndexOf(seq, elem) ==
  IF elem \in SeqToSet(seq) THEN
    CHOOSE i \in 1..Len(seq) : seq[i] = elem
  ELSE -1

\* 6. Converting a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* 7. Getting the last element of a sequence (NULL for empty)
Last(seq) ==
  IF Len(seq) = 0 THEN NULL
  ELSE seq[Len(seq)]

\* 8. Testing if a sequence is empty
SeqIsEmpty(seq) == Len(seq) = 0

\* 9. Removing all occurrences of an element from a sequence
RemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF Head(seq) = elem
       THEN RemoveAll(Tail(seq), elem)
       ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), elem)

\* 10. Computing the intersection of a set of sets
SetIntersection(SS) ==
  IF SS = {} THEN {}
  ELSE
    LET first == CHOOSE s \in SS : TRUE
    IN { x \in first : \A s \in SS : x \in s }

\* 11. Generating all permutation sequences of a finite set
Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE
    UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

\* 12. Test helper for writing assertions that print diagnostic information on failure
TestHelper(pred, msg) ==
  IF pred THEN TRUE
  ELSE Print(msg) /\ FALSE

\* ----------------------------------------------------------------------
\* Trivial specification to satisfy required identifiers
\* ----------------------------------------------------------------------

VARIABLES dummy

Init == TRUE

Next == UNCHANGED dummy

SPECIFICATION == Init /\ [][Next]_<<dummy>>

INVARIANTS == TRUE

PROPERTIES == TRUE

====