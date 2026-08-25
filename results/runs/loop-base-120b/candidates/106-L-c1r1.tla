---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Utility operators
\* ----------------------------------------------------------------------

\* (1) Set intersection test – true iff A and B share at least one element
SetOverlap(A, B) == \E x \in A : x \in B

\* (2) Maximum and minimum element selection from a (numeric) set
SetMax(S) == IF S = {} THEN NULL ELSE Max(S)
SetMin(S) == IF S = {} THEN NULL ELSE Min(S)

\* (3) Generalized set reduction (fold) with binary operator f
RECURSIVE SetFold(_,_,_)
SetFold(S, acc, f) ==
  IF S = {} THEN acc
  ELSE
    LET x == CHOOSE y \in S : TRUE
    IN f(x, SetFold(S \ {x}, acc, f))

\* (4) Sequence reduction (fold) using the library FoldSeq operator
SeqFold(seq, acc, f) == FoldSeq(seq, acc, f)

\* (5) Index of the first occurrence of an element in a sequence
SeqIndex(seq, elem) ==
  IF \E i \in 1..Len(seq) : seq[i] = elem
    THEN CHOOSE i \in 1..Len(seq) : seq[i] = elem
    ELSE -1

\* (6) Convert a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* (7) Last element of a sequence
Last(seq) ==
  IF Len(seq) = 0 THEN NULL ELSE seq[Len(seq)]

\* (8) Test whether a sequence is empty
SeqIsEmpty(seq) == Len(seq) = 0

\* (9) Remove all occurrences of an element from a sequence
RECURSIVE SeqRemoveAll(_,_)
SeqRemoveAll(seq, elem) ==
  IF Len(seq) = 0
    THEN <<>>
    ELSE IF Head(seq) = elem
            THEN SeqRemoveAll(Tail(seq), elem)
            ELSE <<Head(seq)>> \o SeqRemoveAll(Tail(seq), elem)

\* (10) Intersection of a set of sets
SetIntersection(SS) == { x : \A S \in SS : x \in S }

\* (11) Generate all permutations of a finite set
RECURSIVE Permutations(_)
Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

\* (12) Test helper that prints a diagnostic message on failure
Assert(cond, msg) ==
  IF cond THEN TRUE ELSE (Print(msg) ; FALSE)

\* ----------------------------------------------------------------------
\* Stubs required by the (empty) .cfg file
\* ----------------------------------------------------------------------
SPECIFICATION == TRUE
INIT == TRUE
NEXT == UNCHANGED <<>>
INVARIANTS == TRUE
PROPERTIES == TRUE

====