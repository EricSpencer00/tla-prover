---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* 1. Test whether two sets overlap (intersection non‑empty)
SetOverlap(S, T) == (S \cap T) # {}

\* 2. Maximum element of a non‑empty finite set (returns NULL for empty set)
SetMax(S) ==
  IF S = {} THEN
    NULL
  ELSE
    CHOOSE x \in S : \A y \in S : y \le x

\* 3. Minimum element of a non‑empty finite set (returns NULL for empty set)
SetMin(S) ==
  IF S = {} THEN
    NULL
  ELSE
    CHOOSE x \in S : \A y \in S : x \le y

\* 4. Generalized set reduction (fold over a set with accumulator)
SetReduce(S, acc, f(_,_)) ==
  IF S = {} THEN
    acc
  ELSE
    LET e == CHOOSE x \in S : TRUE
    IN SetReduce(S \ {e}, f(acc, e), f)

\* 5. Sequence reduction (fold over a sequence with accumulator)
SeqReduce(seq, acc, f(_,_)) ==
  IF Len(seq) = 0 THEN
    acc
  ELSE
    SeqReduce(Tail(seq), f(acc, Head(seq)), f)

\* 6. Index of the first occurrence of an element in a sequence
SeqIdx(seq, elem) ==
  IF \E i \in 1..Len(seq) : seq[i] = elem THEN
    CHOOSE i \in 1..Len(seq) : seq[i] = elem
  ELSE
    0

\* 7. Convert a sequence to the set of its elements
SeqToSet(seq) ==
  { x \in UNION { { seq[i] } : i \in 1..Len(seq) } : 
      \E i \in 1..Len(seq) : seq[i] = x }

\* 8. Get the last element of a sequence (NULL if empty)
SeqLast(seq) ==
  IF Len(seq) = 0 THEN
    NULL
  ELSE
    seq[Len(seq)]

\* 9. Test whether a sequence is empty
SeqEmpty(seq) == Len(seq) = 0

\* 10. Remove all occurrences of an element from a sequence
SeqRemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN
    <<>>
  ELSE IF Head(seq) = elem THEN
    SeqRemoveAll(Tail(seq), elem)
  ELSE
    <<Head(seq)>> \o SeqRemoveAll(Tail(seq), elem)

\* 11. Intersection of a set of sets
SetIntersectionAll(SS) == INTERSECTION(SS)

\* 12. Generate all permutations of a finite set as sequences
Permutations(S) ==
  IF S = {} THEN
    { <<>> }
  ELSE
    UNION { { <<e>> \o p } : e \in S, p \in Permutations(S \ {e}) }

\* 13. Assertion helper that prints a diagnostic message on failure
AssertHelper(cond, msg) ==
  IF cond THEN
    TRUE
  ELSE
    (Print(msg); FALSE)

====