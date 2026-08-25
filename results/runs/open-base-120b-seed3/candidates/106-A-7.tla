---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Utility operators
\* ----------------------------------------------------------------------

\* 1. Set intersection test: returns TRUE iff S and T overlap.
Overlap(S, T) == \E x \in S : x \in T

\* 2. Maximum and minimum element selection from a non‑empty set.
Max(S) == CHOOSE x \in S : \A y \in S : y <= x
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

\* 3. Generalized set reduction (fold) over a set.
SetReduce(F, acc, S) ==
  IF S = {} THEN acc
  ELSE
    LET e == CHOOSE x \in S : TRUE
    IN SetReduce(F, F(acc, e), S \ {e})

\* 4. Sequence reduction (fold) over a sequence.
SeqReduce(F, acc, seq) ==
  IF Len(seq) = 0 THEN acc
  ELSE SeqReduce(F, F(acc, Head(seq)), Tail(seq))

Head(seq) == seq[1]

Tail(seq) ==
  [i \in 1..(Len(seq) - 1) |-> seq[i + 1]]

\* 5. Index of an element in a sequence (0 if not present).
IndexOf(seq, e) ==
  IF \E i \in 1..Len(seq) : seq[i] = e
    THEN Min({ i \in 1..Len(seq) : seq[i] = e })
    ELSE 0

\* 6. Convert a sequence to the set of its elements.
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* 7. Last element of a non‑empty sequence.
Last(seq) == seq[Len(seq)]

\* 8. Test whether a sequence is empty.
SeqIsEmpty(seq) == Len(seq) = 0

\* 9. Remove all occurrences of an element from a sequence.
RemoveAll(seq, e) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF Head(seq) = e
        THEN RemoveAll(Tail(seq), e)
        ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), e)

\* 10. Intersection of a set of sets.
SetIntersection(Sets) ==
  IF Sets = {} THEN {}
  ELSE
    LET s0 == CHOOSE s \in Sets : TRUE
    IN IntersectRest(s0, Sets \ {s0})

IntersectRest(acc, remaining) ==
  IF remaining = {} THEN acc
  ELSE
    LET s == CHOOSE t \in remaining : TRUE
    IN IntersectRest(acc \cap s, remaining \ {s})

\* 11. All permutations of a finite set.
Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE
    UNION { { <<e>> \o p } :
            e \in S,
            p \in Permutations(S \ {e}) }

\* 12. Assertion helper that prints a diagnostic message on failure.
Assert(cond, msg) ==
  IF cond THEN TRUE ELSE Print(msg) /\ FALSE

\* ----------------------------------------------------------------------
\* Trivial specification skeleton (required identifiers)
\* ----------------------------------------------------------------------
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====