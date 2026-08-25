---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ------------------------------------------------------------
\* Set intersection test: whether two sets overlap
\* ------------------------------------------------------------
SetOverlap(S, T) == (S \cap T) # {}

\* ------------------------------------------------------------
\* Maximum and minimum element selection from a set
\* ------------------------------------------------------------
Max(S) ==
  IF S = {} THEN
    (* no maximum defined for empty set *)
    (* TLC will report an error if this is ever evaluated *)
    CHOOSE x : FALSE
  ELSE
    CHOOSE x \in S : \A y \in S : y <= x

Min(S) ==
  IF S = {} THEN
    CHOOSE x : FALSE
  ELSE
    CHOOSE x \in S : \A y \in S : x <= y

\* ------------------------------------------------------------
\* Generalized set reduction (fold over a set with an accumulator)
\* ------------------------------------------------------------
RECURSIVE SetReduce(_, _, _)
SetReduce(S, acc, op) ==
  IF S = {} THEN
    acc
  ELSE
    LET e == CHOOSE x \in S : TRUE
    IN SetReduce(S \ {e}, op(acc, e), op)

\* ------------------------------------------------------------
\* Sequence reduction (fold over a sequence with an accumulator)
\* ------------------------------------------------------------
RECURSIVE SeqReduce(_, _, _)
SeqReduce(seq, acc, op) ==
  IF Len(seq) = 0 THEN
    acc
  ELSE
    SeqReduce(Tail(seq), op(acc, Head(seq)), op)

\* ------------------------------------------------------------
\* Finding the index of an element in a sequence (1‑based, 0 if not found)
\* ------------------------------------------------------------
RECURSIVE IndexOf(_, _)
IndexOf(seq, elem) ==
  IF Len(seq) = 0 THEN
    0
  ELSE IF Head(seq) = elem THEN
    1
  ELSE
    LET i == IndexOf(Tail(seq), elem)
    IN IF i = 0 THEN 0 ELSE i + 1

\* ------------------------------------------------------------
\* Converting a sequence to the set of its elements
\* ------------------------------------------------------------
SeqToSet(seq) == { seq[i] : i \in DOMAIN seq }

\* ------------------------------------------------------------
\* Getting the last element of a sequence
\* ------------------------------------------------------------
Last(seq) ==
  IF Len(seq) = 0 THEN
    CHOOSE x : FALSE
  ELSE
    seq[Len(seq)]

\* ------------------------------------------------------------
\* Testing if a sequence is empty
\* ------------------------------------------------------------
IsEmpty(seq) == Len(seq) = 0

\* ------------------------------------------------------------
\* Removing all occurrences of an element from a sequence
\* ------------------------------------------------------------
RECURSIVE RemoveAll(_, _)
RemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN
    <<>>
  ELSE
    IF Head(seq) = elem THEN
      RemoveAll(Tail(seq), elem)
    ELSE
      <<Head(seq)>> \o RemoveAll(Tail(seq), elem)

\* ------------------------------------------------------------
\* Computing the intersection of a set of sets
\* ------------------------------------------------------------
SetIntersection(SS) ==
  IF SS = {} THEN {} ELSE INTERSECTION(SS)

\* ------------------------------------------------------------
\* Generating all permutation sequences of a finite set
\* ------------------------------------------------------------
RECURSIVE Permutations(_)
Permutations(S) ==
  IF S = {} THEN
    { <<>> }
  ELSE
    UNION { { <<e>> \o p } : e \in S, p \in Permutations(S \ {e}) }

\* ------------------------------------------------------------
\* Test helper for writing assertions that print diagnostic information on failure
\* ------------------------------------------------------------
Assert(cond, msg) ==
  IF cond THEN TRUE
  ELSE (Print(msg); FALSE)

====