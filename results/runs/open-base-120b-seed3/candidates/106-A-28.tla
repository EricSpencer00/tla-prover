---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Set intersection test (whether two sets overlap)
\* ----------------------------------------------------------------------
SetOverlap(S, T) == (S \cap T) # {}

\* ----------------------------------------------------------------------
\* Maximum and minimum element selection from a set (numeric sets)
\* ----------------------------------------------------------------------
SetMax(S) == 
  IF S = {} THEN NULL
  ELSE Max(S)

SetMin(S) == 
  IF S = {} THEN NULL
  ELSE Min(S)

\* ----------------------------------------------------------------------
\* Generalized set reduction (fold over a set with an accumulator)
\* ----------------------------------------------------------------------
SetFold(S, init, f) ==
  IF S = {} THEN init
  ELSE
    LET x == CHOOSE e \in S : TRUE
    IN SetFold(S \ {x}, f(init, x), f)

\* ----------------------------------------------------------------------
\* Sequence reduction (fold over a sequence with an accumulator)
\* ----------------------------------------------------------------------
SeqFold(seq, init, f) ==
  IF Len(seq) = 0 THEN init
  ELSE SeqFold(Tail(seq), f(init, Head(seq)), f)

\* ----------------------------------------------------------------------
\* Finding the index of an element in a sequence (1‑based, 0 if not found)
\* ----------------------------------------------------------------------
SeqIndex(seq, elem) ==
  LET Rec(s, i) ==
    IF Len(s) = 0 THEN 0
    ELSE IF Head(s) = elem THEN i
    ELSE Rec(Tail(s), i + 1)
  IN Rec(seq, 1)

\* ----------------------------------------------------------------------
\* Converting a sequence to the set of its elements
\* ----------------------------------------------------------------------
SeqToSet(seq) == { e : e \in seq }

\* ----------------------------------------------------------------------
\* Getting the last element of a sequence
\* ----------------------------------------------------------------------
SeqLast(seq) ==
  IF Len(seq) = 0 THEN NULL
  ELSE Head(Reverse(seq))

\* ----------------------------------------------------------------------
\* Testing if a sequence is empty
\* ----------------------------------------------------------------------
SeqIsEmpty(seq) == Len(seq) = 0

\* ----------------------------------------------------------------------
\* Removing all occurrences of an element from a sequence
\* ----------------------------------------------------------------------
SeqRemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF Head(seq) = elem THEN SeqRemoveAll(Tail(seq), elem)
  ELSE <<Head(seq)>> \o SeqRemoveAll(Tail(seq), elem)

\* ----------------------------------------------------------------------
\* Computing the intersection of a set of sets
\* ----------------------------------------------------------------------
SetIntersection(SS) == \cap SS

\* ----------------------------------------------------------------------
\* Generating all permutation sequences of a finite set
\* ----------------------------------------------------------------------
SetPermutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE UNION { { <<x>> \o p } : x \in S, p \in SetPermutations(S \ {x}) }

\* ----------------------------------------------------------------------
\* Test helper for writing assertions that print diagnostic information
\* ----------------------------------------------------------------------
TestHelper(msg, cond) ==
  IF cond THEN TRUE
  ELSE
    /\ FALSE
    /\ Print(msg)

\* ----------------------------------------------------------------------
\* Trivial specification skeleton (required identifiers)
\* ----------------------------------------------------------------------
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====