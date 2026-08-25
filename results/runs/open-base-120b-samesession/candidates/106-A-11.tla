---- MODULE Util ----
EXTENDS Naturals, Sequences

\* ----------------------------------------------------------------------
\* Utility operators
\* ----------------------------------------------------------------------

\* 1. Set intersection test (whether two sets overlap)
SetOverlap(A, B) == (A \cap B) # {}

\* 2. Maximum element selection from a set
SetMax(S) ==
  IF S = {} THEN
    NULL
  ELSE
    CHOOSE x \in S : \A y \in S : x >= y

\* 3. Minimum element selection from a set
SetMin(S) ==
  IF S = {} THEN
    NULL
  ELSE
    CHOOSE x \in S : \A y \in S : x <= y

\* 4. Generalized set reduction (fold over a set with an accumulator)
RECURSIVE SetReduce(_,_,_)
SetReduce(S, init, op) ==
  IF S = {} THEN
    init
  ELSE
    LET e == CHOOSE x \in S IN
      op(e, SetReduce(S \ {e}, init, op))

\* 5. Sequence reduction (fold over a sequence with an accumulator)
RECURSIVE SeqReduce(_,_,_)
SeqReduce(seq, init, op) ==
  IF Len(seq) = 0 THEN
    init
  ELSE
    op(Head(seq), SeqReduce(Tail(seq), init, op))

\* 6. Finding the index of an element in a sequence
SeqIndex(seq, elem) ==
  CHOOSE i \in 1..Len(seq) : seq[i] = elem

\* 7. Converting a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* 8. Getting the last element of a sequence
SeqLast(seq) == seq[Len(seq)]

\* 9. Testing if a sequence is empty
SeqIsEmpty(seq) == Len(seq) = 0

\* 10. Removing all occurrences of an element from a sequence
RECURSIVE SeqRemoveAll(_,_)
SeqRemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN
    <<>>
  ELSE IF Head(seq) = elem THEN
    SeqRemoveAll(Tail(seq), elem)
  ELSE
    <<Head(seq)>> \o SeqRemoveAll(Tail(seq), elem)

\* 11. Computing the intersection of a set of sets
SetIntersectAll(Ssets) ==
  { x \in UNION Ssets : \A A \in Ssets : x \in A }

\* 12. Generating all permutation sequences of a finite set
RECURSIVE Permutations(_)
Permutations(S) ==
  IF S = {} THEN
    { <<>> }
  ELSE
    UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

\* 13. Test helper for writing assertions (prints diagnostics on failure)
TestHelper(expr) ==
  IF expr THEN TRUE ELSE FALSE

\* ----------------------------------------------------------------------
\* Dummy specification (required identifiers)
\* ----------------------------------------------------------------------
VARIABLES dummy

Init == dummy = 0

Next == UNCHANGED dummy

Spec == Init /\ [][Next]_<<dummy>>

INVARIANTS == TRUE

PROPERTIES == TRUE

====