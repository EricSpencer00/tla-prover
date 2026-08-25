---- MODULE Util ----
EXTENDS Naturals, Sequences, TLC

\* Set overlap test (whether two sets intersect)
SetOverlap(S, T) == ~(S \cap T = {})

\* Maximum element of a non‑empty set (assumes a total order on the elements)
SetMax(S) ==
  IF S = {} THEN NULL
  ELSE CHOOSE x \in S : \A y \in S : x >= y

\* Minimum element of a non‑empty set (assumes a total order on the elements)
SetMin(S) ==
  IF S = {} THEN NULL
  ELSE CHOOSE x \in S : \A y \in S : x <= y

\* Generalized set reduction (fold over a set with an accumulator)
RECURSIVE SetReduce(_, _, _)
SetReduce(S, acc, f) ==
  IF S = {} THEN acc
  ELSE
    LET e == CHOOSE x \in S IN
      SetReduce(S \ {e}, f(acc, e), f)

\* Sequence reduction (fold over a sequence with an accumulator, using FoldSeq)
SeqReduce(seq, acc, f) == FoldSeq(seq, acc, f)

\* Index of the first occurrence of an element in a sequence (1‑based, 0 if absent)
RECURSIVE IndexOf(_, _)
IndexOf(seq, elem) ==
  IF seq = <<>> THEN 0
  ELSE IF Head(seq) = elem THEN 1
  ELSE
    LET i == IndexOf(Tail(seq), elem) IN
      IF i = 0 THEN 0 ELSE i + 1

\* Convert a sequence to a set containing the same elements
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* Last element of a sequence (NULL if the sequence is empty)
Last(seq) ==
  IF Len(seq) = 0 THEN NULL
  ELSE seq[Len(seq)]

\* Test whether a sequence is empty
IsEmpty(seq) == Len(seq) = 0

\* Remove all occurrences of an element from a sequence
RECURSIVE RemoveAll(_, _)
RemoveAll(seq, elem) ==
  IF seq = <<>> THEN <<>>
  ELSE IF Head(seq) = elem THEN RemoveAll(Tail(seq), elem)
  ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), elem)

\* Intersection of a set of sets
SetIntersection(SS) ==
  IF SS = {} THEN {} ELSE INTERSECTION SS

\* Generate all permutations of a finite set as sequences
RECURSIVE Permutations(_)
Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

\* Test helper that prints a diagnostic message on failure
TestHelper(cond, msg) ==
  IF cond THEN TRUE ELSE (Print(msg) /\ FALSE)

====