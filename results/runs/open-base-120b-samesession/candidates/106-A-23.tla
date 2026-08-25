---- MODULE Util ----
EXTENDS Naturals, Sequences, TLC

\* ------------------------------------------------------------
\* Utility operators
\* ------------------------------------------------------------

\* (1) Set intersection test (whether two sets overlap)
SetOverlap(S, T) == \E x \in S : x \in T

\* (2) Maximum element of a non‑empty set
MaxSet(S) == 
  CHOOSE x \in S :
    \A y \in S : y <= x

\* (2) Minimum element of a non‑empty set
MinSet(S) == 
  CHOOSE x \in S :
    \A y \in S : x <= y

\* (3) Generalized set reduction (fold over a set with an accumulator)
SetReduce(S, op, a) ==
  IF S = {} THEN a
  ELSE
    LET x == CHOOSE y \in S
    IN SetReduce(S \ {x}, op, op(a, x))

\* (4) Sequence reduction (fold over a sequence with an accumulator)
SeqReduce(seq, op, a) ==
  IF Len(seq) = 0 THEN a
  ELSE SeqReduce(Tail(seq), op, op(a, Head(seq)))

\* (5) Find the index (1‑based) of the first occurrence of an element in a sequence
SeqIndex(seq, e) ==
  IF e \in SeqSet(seq) THEN
    CHOOSE i \in 1..Len(seq) : seq[i] = e
  ELSE 0

\* (6) Convert a sequence to the set of its elements
SeqSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* (7) Get the last element of a non‑empty sequence
Last(seq) == seq[Len(seq)]

\* (8) Test if a sequence is empty
SeqIsEmpty(seq) == Len(seq) = 0

\* (9) Remove all occurrences of an element from a sequence, preserving order
RemoveAll(seq, e) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF Head(seq) = e THEN RemoveAll(Tail(seq), e)
  ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), e)

\* (10) Intersection of a set of sets
SetIntersectionOfSets(SS) ==
  { x \in UNION SS : \A S \in SS : x \in S }

\* (11) All permutations of a finite set
Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

\* (12) Test helper that prints a message on failure
TestHelper(cond, msg) ==
  IF cond THEN TRUE ELSE (Print(msg); FALSE)

\* ------------------------------------------------------------
\* Dummy specification to satisfy required identifiers
\* ------------------------------------------------------------

Init == TRUE

Next == UNCHANGED {}

Spec == Init /\ [][Next]_<<>>

INVARIANTS == {}

PROPERTIES == {}

====