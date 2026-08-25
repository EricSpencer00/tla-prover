---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

VARIABLES dummy

\* -------------------------------------------------
\* Utility operators
\* -------------------------------------------------

\* 1. Set intersection test (whether two sets overlap)
SetOverlap(S, T) == S \cap T # {}

\* 2. Maximum element of a non‑empty set
SetMax(S) == CHOOSE x \in S : \A y \in S : y <= x

\* 3. Minimum element of a non‑empty set
SetMin(S) == CHOOSE x \in S : \A y \in S : x <= y

\* 4. Generalized set reduction (fold over a set with an accumulator)
SetReduce(S, a, f) ==
  IF S = {} THEN a
  ELSE LET x == CHOOSE e \in S IN SetReduce(S \ {x}, f(a, x), f)

\* 5. Sequence reduction (fold over a sequence with an accumulator)
SeqReduce(seq, a, f) ==
  IF Len(seq) = 0 THEN a
  ELSE SeqReduce(Tail(seq), f(a, Head(seq)), f)

\* 6. Finding the index of an element in a sequence (0 if not present)
IndexOf(seq, e) ==
  IF e \in SeqToSet(seq) THEN
    CHOOSE i \in 1..Len(seq) : seq[i] = e
  ELSE 0

\* 7. Converting a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* 8. Getting the last element of a sequence (NULL if empty)
Last(seq) ==
  IF Len(seq) = 0 THEN NULL ELSE seq[Len(seq)]

\* 9. Testing if a sequence is empty
IsEmpty(seq) == Len(seq) = 0

\* 10. Removing all occurrences of an element from a sequence
RemoveAll(seq, e) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF Head(seq) = e THEN RemoveAll(Tail(seq), e)
  ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), e)

\* 11. Computing the intersection of a set of sets
SetIntersection(SS) == { x : \A s \in SS : x \in s }

\* 12. Generating all permutation sequences of a finite set
Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

\* 13. Test helper for assertions with diagnostic output
TestHelper(cond, msg) ==
  IF cond THEN TRUE ELSE (Print(msg); FALSE)

\* -------------------------------------------------
\* Specification scaffolding (required identifiers)
\* -------------------------------------------------

Init == dummy = TRUE

Next == UNCHANGED dummy

SPECIFICATION == Init /\ [][Next]_<<dummy>>

INVARIANTS == {}

PROPERTIES == {}

====