---- MODULE Util ----
EXTENDS Naturals, Sequences, TLC

\* 1. Set intersection test (whether two sets overlap)
Overlap(S, T) == \E x \in S : x \in T

\* 2. Maximum element selection from a set (returns NULL on empty set)
SetMax(S) ==
  IF S = {} THEN
    NULL
  ELSE
    CHOOSE x \in S : \A y \in S : y <= x

\* 2b. Minimum element selection from a set (returns NULL on empty set)
SetMin(S) ==
  IF S = {} THEN
    NULL
  ELSE
    CHOOSE x \in S : \A y \in S : x <= y

\* 3. Generalized set reduction (fold over a set with an accumulator)
\*    op is a binary operator supplied as a two‑argument function.
SetReduce(S, acc, op(_,_)) ==
  IF S = {} THEN
    acc
  ELSE
    LET e == CHOOSE x \in S
    IN SetReduce(S \ {e}, op(acc, e), op)

\* 4. Sequence reduction (fold over a sequence with an accumulator)
SeqReduce(seq, acc, op(_,_)) ==
  IF Len(seq) = 0 THEN
    acc
  ELSE
    SeqReduce(SeqTail(seq), op(acc, SeqHead(seq)), op)

\* 5. Finding the index of an element in a sequence (0 if not present)
IndexOf(seq, elem) ==
  IF elem \in SeqToSet(seq) THEN
    CHOOSE i \in 1..Len(seq) : seq[i] = elem
  ELSE
    0

\* 6. Converting a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* 7. Getting the last element of a sequence (NULL if empty)
Last(seq) ==
  IF Len(seq) = 0 THEN
    NULL
  ELSE
    seq[Len(seq)]

\* 8. Testing if a sequence is empty
IsEmpty(seq) == Len(seq) = 0

\* 9. Removing all occurrences of an element from a sequence
RemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN
    <<>>
  ELSE IF SeqHead(seq) = elem THEN
    RemoveAll(SeqTail(seq), elem)
  ELSE
    <<SeqHead(seq)>> \o RemoveAll(SeqTail(seq), elem)

\* 10. Computing the intersection of a set of sets
SetIntersection(SS) ==
  IF SS = {} THEN
    {}
  ELSE
    { x \in UNION(SS) : \A S \in SS : x \in S }

\* 11. Generating all permutation sequences of a finite set
Permutations(S) ==
  IF S = {} THEN
    { <<>> }
  ELSE
    UNION { { <<e>> \o p : p \in Permutations(S \ {e}) } : e \in S }

\* 12. Test helper for writing assertions that print diagnostic information on failure
TestHelper(cond, msg) ==
  IF cond THEN
    TRUE
  ELSE
    (Print(msg); FALSE)

====