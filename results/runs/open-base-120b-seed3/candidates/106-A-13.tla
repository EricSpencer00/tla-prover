---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ------------------------------------------------------------
\* Utility operators
\* ------------------------------------------------------------

\* (1) Set intersection test: returns TRUE iff two sets overlap
SetOverlap(S, T) == \E x \in S : x \in T

\* (2) Maximum element of a (non‑empty) set; NULL for the empty set
SetMax(S) ==
  IF S = {} THEN NULL
  ELSE CHOOSE x \in S: \A y \in S: y <= x

\* (2) Minimum element of a set; NULL for the empty set
SetMin(S) ==
  IF S = {} THEN NULL
  ELSE CHOOSE x \in S: \A y \in S: y >= x

\* (3) Generalized set reduction (fold) over a set
RECURSIVE SetReduce(_,_,_)
SetReduce(S, f, a) ==
  IF S = {} THEN a
  ELSE
    LET x == CHOOSE y \in S: TRUE
    IN SetReduce(S \ {x}, f, f(a, x))

\* (4) Sequence reduction (fold) using TLC's built‑in FoldSeq
SeqReduce(seq, f, a) == TLC!FoldSeq(seq, f, a)

\* (5) Index of the first occurrence of an element in a sequence
\* Returns -1 if the element is not present
SeqIndex(seq, e) ==
  IF \E i \in DOMAIN seq: seq[i] = e THEN
    CHOOSE i \in DOMAIN seq: seq[i] = e
  ELSE -1

\* (6) Convert a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in DOMAIN seq }

\* (7) Last element of a sequence; NULL for the empty sequence
SeqLast(seq) ==
  IF seq = <<>> THEN NULL
  ELSE seq[Len(seq)]

\* (8) Test whether a sequence is empty
SeqIsEmpty(seq) == seq = <<>>

\* (9) Remove all occurrences of an element from a sequence
RECURSIVE SeqRemoveAll(_,_)
SeqRemoveAll(seq, e) ==
  IF seq = <<>> THEN <<>>
  ELSE IF Head(seq) = e THEN SeqRemoveAll(Tail(seq), e)
  ELSE <<Head(seq)>> \o SeqRemoveAll(Tail(seq), e)

\* (10) Intersection of a (possibly empty) set of sets
SetIntersectionOfSetOfSets(SS) ==
  IF SS = {} THEN {}
  ELSE \INTERSECTION SS

\* (11) All permutations of a finite set (as sequences)
Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

\* (12) Test helper that prints a message on failure
TestHelper(expr, msg) ==
  IF expr THEN TRUE
  ELSE Print(msg) /\ FALSE

\* ------------------------------------------------------------
\* Place‑holder identifiers required by the generic template
\* ------------------------------------------------------------

SPECIFICATION == TRUE
INIT == TRUE
NEXT == UNCHANGED {}
INVARIANTS == TRUE
PROPERTIES == TRUE

====