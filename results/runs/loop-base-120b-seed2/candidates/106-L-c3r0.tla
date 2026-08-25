---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\*-------------------- Utility Operators --------------------

\* (1) Set intersection test: whether two sets overlap
Overlap(S, T) == \E x \in S : x \in T

\* (2) Maximum element of a set (returns NULL on empty set)
SetMax(S) ==
  IF S = {} THEN
    NULL
  ELSE
    CHOOSE x \in S :
      \A y \in S : y <= x

\* (2) Minimum element of a set (returns NULL on empty set)
SetMin(S) ==
  IF S = {} THEN
    NULL
  ELSE
    CHOOSE x \in S :
      \A y \in S : x <= y

\* (3) Generalized set reduction (fold over a set with an accumulator)
SetFold(S, init, f(_,_)) ==
  IF S = {} THEN
    init
  ELSE
    LET x == CHOOSE y \in S IN
      SetFold(S \ {x}, f(init, x), f)

\* (4) Sequence reduction (fold over a sequence with an accumulator)
SeqFold(seq, init, f(_,_)) ==
  IF Len(seq) = 0 THEN
    init
  ELSE
    SeqFold(Tail(seq), f(init, Head(seq)), f)

\* (5) Finding the index of an element in a sequence (0 if not present)
SeqIndex(seq, elem) ==
  IF elem \in SeqToSet(seq) THEN
    CHOOSE i \in 1..Len(seq) : seq[i] = elem
  ELSE
    0

\* (6) Converting a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* (7) Getting the last element of a non‑empty sequence
SeqLast(seq) ==
  IF Len(seq) = 0 THEN
    NULL
  ELSE
    seq[Len(seq)]

\* (8) Testing if a sequence is empty
SeqIsEmpty(seq) == Len(seq) = 0

\* (9) Removing all occurrences of an element from a sequence
SeqRemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN
    <<>>
  ELSE IF Head(seq) = elem THEN
    SeqRemoveAll(Tail(seq), elem)
  ELSE
    <<Head(seq)>> \o SeqRemoveAll(Tail(seq), elem)

\* (10) Computing the intersection of a set of sets
SetIntersection(SS) == { x : \A S \in SS : x \in S }

\* (11) Generating all permutation sequences of a finite set
Permutations(S) ==
  IF S = {} THEN
    { <<>> }
  ELSE
    UNION { { <<e>> \o p } : e \in S, p \in Permutations(S \ {e}) }

\* (12) Test helper for assertions that prints diagnostic info on failure
TestHelper(cond, msg) ==
  IF cond THEN
    TRUE
  ELSE
    (Print(msg) /\ FALSE)

\*-------------------- Dummy Specification Elements --------------------
\* (These are provided as placeholders; the library itself has no state.)

SPECIFICATION == TRUE
INIT == TRUE
NEXT == UNCHANGED << >>
INVARIANTS == {}
PROPERTIES == {}

====