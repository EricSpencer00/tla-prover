---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Utility operators
\* ----------------------------------------------------------------------

\* 1) Set intersection test (whether two sets overlap)
SetOverlap(A, B) == (A \cap B) # {}

\* 2) Maximum element of a non‑empty set (assumes elements are comparable)
SetMax(S) == 
  CHOOSE x \in S : \A y \in S : y <= x

\*    Minimum element of a non‑empty set
SetMin(S) == 
  CHOOSE x \in S : \A y \in S : x <= y

\* 3) Generalized set reduction (fold over a set with an accumulator)
\*    F is a binary operator, init is the initial accumulator value
SetFold(F, init, S) ==
  IF S = {} THEN init
  ELSE
    LET e == CHOOSE x \in S IN
      SetFold(F, F(init, e), S \ {e})

\* 4) Sequence reduction (fold over a sequence with an accumulator)
\*    Uses the library operator FoldSeq from the Sequences module
SeqFold(F, init, seq) == FoldSeq(F, init, seq)

\* 5) Index of an element in a sequence (returns 0 if not found)
IndexOf(seq, elem) ==
  IF \E i \in DOMAIN seq : seq[i] = elem
  THEN CHOOSE i \in DOMAIN seq : seq[i] = elem
  ELSE 0

\* 6) Convert a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in DOMAIN seq }

\* 7) Last element of a non‑empty sequence
Last(seq) == seq[Len(seq)]

\* 8) Test if a sequence is empty
SeqIsEmpty(seq) == Len(seq) = 0

\* 9) Remove all occurrences of an element from a sequence
RemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF Head(seq) = elem
       THEN RemoveAll(Tail(seq), elem)
       ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), elem)

\* 10) Intersection of a set of sets
SetIntersection(SS) ==
  IF SS = {} THEN {}
  ELSE
    LET S0 == CHOOSE S \in SS IN
      { x \in S0 : \A S \in SS : x \in S }

\* 11) All permutations of a finite set
SetPermutations(S) == Permutations(S)

\* 12) Assertion helper that prints a diagnostic message on failure
Assert(cond, msg) ==
  IF cond THEN TRUE
  ELSE (Print(msg); FALSE)

\* ----------------------------------------------------------------------
\* Trivial specification scaffolding (required by the .cfg)
\* ----------------------------------------------------------------------
VARIABLES dummy

Init == dummy = 0

Next == UNCHANGED dummy

SPECIFICATION == Init /\ [][Next]_<<dummy>>

INVARIANTS == TRUE

PROPERTIES == TRUE

=============================================================================