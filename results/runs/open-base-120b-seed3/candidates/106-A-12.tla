---- MODULE Util ----
EXTENDS Naturals, Sequences, TLC

\* 1. Test whether two sets overlap
SetOverlap(s, t) == ∃ x \in s : x \in t

\* 2. Maximum element of a (totally ordered) set
SetMax(S) ==
  IF S = {} THEN
    NULL
  ELSE
    CHOOSE x \in S :
      \A y \in S : y <= x

\* 3. Minimum element of a (totally ordered) set
SetMin(S) ==
  IF S = {} THEN
    NULL
  ELSE
    CHOOSE x \in S :
      \A y \in S : x <= y

\* 4. Generalized reduction (fold) over a set
\*    f is a binary operator, init is the initial accumulator value
SetReduce(S, f, init) ==
  IF S = {} THEN
    init
  ELSE
    LET e == CHOOSE x \in S IN
      SetReduce(S \ {e}, f, f(e, init))

\* 5. Reduction over a sequence (fold) using the built‑in FoldSeq operator
\*    SeqReduce(seq, f, init) returns the result of folding f over seq
SeqReduce(seq, f, init) ==
  IF Len(seq) = 0 THEN
    init
  ELSE
    f(seq[1], SeqReduce(SubSeq(seq, 2, Len(seq)), f, init))

\* 6. Find the (first) index of element e in a sequence
SeqIndex(seq, e) ==
  IF \E i \in 1..Len(seq) : seq[i] = e THEN
    CHOOSE i \in 1..Len(seq) : seq[i] = e
  ELSE
    -1

\* 7. Convert a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* 8. Return the last element of a sequence (NULL if empty)
SeqLast(seq) ==
  IF Len(seq) = 0 THEN
    NULL
  ELSE
    seq[Len(seq)]

\* 9. Test whether a sequence is empty
SeqIsEmpty(seq) == Len(seq) = 0

\* 10. Remove all occurrences of element e from a sequence
SeqRemoveAll(seq, e) ==
  IF Len(seq) = 0 THEN
    <<>>
  ELSE IF seq[1] = e THEN
    SeqRemoveAll(SubSeq(seq, 2, Len(seq)), e)
  ELSE
    <<seq[1]>> \o SeqRemoveAll(SubSeq(seq, 2, Len(seq)), e)

\* 11. Intersection of a set of sets
SetIntersection(SS) ==
  { x \in UNION SS : \A A \in SS : x \in A }

\* 12. Generate all permutations of a finite set
Permutations(S) ==
  IF S = {} THEN
    { <<>> }
  ELSE
    UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

\* 13. Test helper that prints a diagnostic message on failure (uses TLC's Assert)
TestHelper(cond, msg) == Assert(cond, msg)

====