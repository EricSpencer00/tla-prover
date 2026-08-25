---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\* Utility operators used throughout the key‑value store specifications.
\* ----------------------------------------------------------------------

\* 1. Set overlap test: true iff A and B share at least one element.
SetOverlap(A, B) == \E x \in A : x \in B

\* 2. Maximum element of a non‑empty finite set (assumes a total order on the elements).
SetMax(S) == 
  IF S = {} THEN @
  ELSE CHOOSE x \in S : \A y \in S : y <= x

\* 3. Minimum element of a non‑empty finite set.
SetMin(S) == 
  IF S = {} THEN @
  ELSE CHOOSE x \in S : \A y \in S : x <= y

\* 4. Generalized reduction (fold) over a set.
\*    f is a binary operator: f(element, accumulator) \in T.
SetReduce(S, init, f) ==
  IF S = {} THEN init
  ELSE
    LET a == CHOOSE x \in S IN
      f(a, SetReduce(S \ {a}, init, f))

\* 5. Reduction (fold) over a sequence.
\*    f is a binary operator: f(element, accumulator) \in T.
SeqReduce(seq, init, f) ==
  IF Len(seq) = 0 THEN init
  ELSE f(seq[1], SeqReduce(Tail(seq), init, f))

\* 6. Index (1‑based) of the first occurrence of elem in seq; 0 if not present.
SeqIndex(seq, elem) ==
  IF \E i \in 1..Len(seq) : seq[i] = elem THEN
    CHOOSE i \in 1..Len(seq) : seq[i] = elem
  ELSE 0

\* 7. Convert a sequence to the set of its elements.
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* 8. Last element of a non‑empty sequence.
SeqLast(seq) ==
  IF Len(seq) = 0 THEN @
  ELSE seq[Len(seq)]

\* 9. Test whether a sequence is empty.
SeqIsEmpty(seq) == Len(seq) = 0

\* 10. Remove all occurrences of elem from seq.
SeqRemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF seq[1] = elem THEN SeqRemoveAll(Tail(seq), elem)
       ELSE << seq[1] >> \o SeqRemoveAll(Tail(seq), elem)

\* 11. Intersection of a set of sets (finite).
SetIntersection(SS) ==
  IF SS = {} THEN {}
  ELSE \INTERSECTION SS

\* 12. All permutations of a finite set S, returned as a set of sequences.
Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE { <<a>> \o p : a \in S, p \in Permutations(S \ {a}) }

\* 13. Assertion helper that prints a diagnostic message on failure.
Assert(cond, msg) ==
  IF cond THEN TRUE
  ELSE (Print(msg); FALSE)

====