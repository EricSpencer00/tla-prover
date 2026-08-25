---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ------------------------------------------------------------
\* Utility operators
\* ------------------------------------------------------------

\* (1) Set intersection test (whether two sets overlap)
Overlap(S, T) == \E x \in S : x \in T

\* (2) Maximum element selection from a set
SetMax(S) ==
  IF S = {} THEN NULL
  ELSE CHOOSE x \in S : \A y \in S : y <= x

\* (2) Minimum element selection from a set
SetMin(S) ==
  IF S = {} THEN NULL
  ELSE CHOOSE x \in S : \A y \in S : y >= x

\* (3) Generalized set reduction (fold over a set with an accumulator)
SetFold(S, init, f) ==
  IF S = {} THEN init
  ELSE
    LET x == CHOOSE y \in S : TRUE IN
      f(x, SetFold(S \\ {x}, init, f))

\* (4) Sequence reduction (fold over a sequence with an accumulator)
SeqFold(seq, init, f) ==
  IF Len(seq) = 0 THEN init
  ELSE f(seq[1], SeqFold(Tail(seq), init, f))

\* (5) Finding the index of an element in a sequence (returns -1 if not found)
IndexOf(seq, elem) ==
  IF \E i \in 1..Len(seq) : seq[i] = elem THEN
    CHOOSE i \in 1..Len(seq) : seq[i] = elem
  ELSE -1

\* (6) Converting a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* (7) Getting the last element of a sequence (undefined if empty)
Last(seq) == seq[Len(seq)]

\* (8) Testing if a sequence is empty
IsEmpty(seq) == Len(seq) = 0

\* (9) Removing all occurrences of an element from a sequence
RemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF seq[1] = elem THEN RemoveAll(Tail(seq), elem)
  ELSE <<seq[1]>> \o RemoveAll(Tail(seq), elem)

\* (10) Computing the intersection of a set of sets
SetIntersection(Sets) ==
  IF Sets = {} THEN {}
  ELSE
    LET first == CHOOSE A \in Sets : TRUE IN
      SetFold(Sets \\ {first}, first, (a, b) -> a \cap b)

\* (11) Generating all permutation sequences of a finite set
Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE { <<x>> \o p : x \in S, p \in Permutations(S \\ {x}) }

\* (12) Test helper for writing assertions that print diagnostic information on failure
TestHelper(cond, msg) ==
  IF cond THEN TRUE
  ELSE (Print(msg) /\ FALSE)

\* ------------------------------------------------------------
\* Required identifiers for the configuration (trivial definitions)
\* ------------------------------------------------------------

SPECIFICATION == TRUE
INIT == TRUE
NEXT == UNCHANGED {}
INVARIANTS == TRUE
PROPERTIES == TRUE

====