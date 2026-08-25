---- MODULE Util ----
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

\*=============================================================
\* Utility operators
\*=============================================================

\* 1. Set intersection test (whether two sets overlap)
Overlap(S, T) == \E x \in S : x \in T

\* 2. Maximum element selection from a set (assumes comparable elements)
SetMax(S) ==
  IF S = {} THEN
    NULL
  ELSE
    CHOOSE x \in S : \A y \in S : y <= x

\* 2b. Minimum element selection from a set
SetMin(S) ==
  IF S = {} THEN
    NULL
  ELSE
    CHOOSE x \in S : \A y \in S : y >= x

\* 3. Generalized set reduction (fold over a set with an accumulator)
SetReduce(S, init, f) ==
  IF S = {} THEN
    init
  ELSE
    LET x == CHOOSE y \in S : TRUE
    IN SetReduce(S \ {x}, f(init, x), f)

\* 4. Sequence reduction (fold over a sequence with an accumulator)
SeqReduce(seq, init, f) == FoldSeq(seq, init, f)

\* 5. Finding the index of an element in a sequence (1‑based)
SeqIndex(seq, elem) ==
  IF elem \in seq THEN
    CHOOSE i \in DOMAIN seq : seq[i] = elem
  ELSE
    NULL

\* 6. Converting a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in DOMAIN seq }

\* 7. Getting the last element of a sequence
SeqLast(seq) ==
  IF Len(seq) = 0 THEN
    NULL
  ELSE
    seq[Len(seq)]

\* 8. Testing if a sequence is empty
SeqIsEmpty(seq) == Len(seq) = 0

\* 9. Removing all occurrences of an element from a sequence
SeqRemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN
    <<>>
  ELSE IF seq[1] = elem THEN
    SeqRemoveAll(Tail(seq), elem)
  ELSE
    << seq[1] >> \o SeqRemoveAll(Tail(seq), elem)

Tail(seq) == [i \in 1..(Len(seq)-1) |-> seq[i+1]]

\* 10. Computing the intersection of a set of sets
SetIntersection(SS) ==
  { x \in UNION SS : \A S \in SS : x \in S }

\* 11. Generating all permutation sequences of a finite set
Permutations(S) ==
  IF S = {} THEN
    { <<>> }
  ELSE
    UNION { << e >> \o p :
               e \in S,
               p \in Permutations(S \ {e}) }

\* 12. Test helper for writing assertions that print diagnostic information
TestHelper(cond) ==
  IF cond THEN
    TRUE
  ELSE
    (Print("ASSERTION FAILED: ", cond) /\ FALSE)

\*=============================================================
\* Required spec identifiers (provided as trivial defaults)
\*=============================================================
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====