---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* -----------------------------
\* Utility operators
\* -----------------------------

\* (1) Set intersection test (whether two sets overlap)
SetIntersect?(S, T) == (S \cap T) # {}

\* (2) Maximum element selection from a set (non‑empty finite set)
SetMax(S) == CHOOSE x \in S : \A y \in S : y <= x

\* (3) Minimum element selection from a set (non‑empty finite set)
SetMin(S) == CHOOSE x \in S : \A y \in S : y >= x

\* (4) Generalized set reduction (fold over a set with an accumulator)
RECURSIVE SetReduce(_,_ ,_)
SetReduce(S, init, f) ==
  IF S = {} THEN init
  ELSE
    LET e == CHOOSE x \in S : TRUE
    IN SetReduce(S \ {e}, f(init, e), f)

\* (5) Sequence reduction (fold over a sequence with an accumulator)
SeqReduce(seq, init, f) == FoldSeq(seq, init, f)

\* (6) Finding the index of an element in a sequence
IndexOf(seq, elem) ==
  IF \E i \in 1..Len(seq) : seq[i] = elem
  THEN CHOOSE i \in 1..Len(seq) : seq[i] = elem
  ELSE 0

\* (7) Converting a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* (8) Getting the last element of a sequence
Last(seq) ==
  IF Len(seq) = 0 THEN {} ELSE seq[Len(seq)]

\* (9) Testing if a sequence is empty
IsEmpty(seq) == Len(seq) = 0

\* (10) Removing all occurrences of an element from a sequence
RemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF seq[1] = elem
       THEN RemoveAll(Tail(seq), elem)
       ELSE <<seq[1]>> \o RemoveAll(Tail(seq), elem)

\* (11) Computing the intersection of a set of sets
SetIntersection(S) == INTERSECTION S

\* (12) Generating all permutation sequences of a finite set
RECURSIVE Permutations(_)
Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

\* (13) Test helper for writing assertions that print diagnostic information on failure
TestHelper(cond, msg) ==
  IF cond THEN TRUE ELSE PrintT(msg) /\ FALSE

\* -------------------------------------------------
\* Trivial specification required identifiers
\* -------------------------------------------------

VARIABLE dummy

Init == dummy = 0

Next == UNCHANGED dummy

SPECIFICATION == Init /\ [] [Next]_<<dummy>>

INIT == Init

NEXT == Next

INVARIANTS == TRUE

PROPERTIES == TRUE

====