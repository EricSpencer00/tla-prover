---- MODULE Util ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Utility operators
\* ----------------------------------------------------------------------
\* 1. Set intersection test (whether two sets overlap)
Overlaps(S, T) == ∃ x \in S : x \in T

\* 2. Maximum and minimum element selection from a set
Max(S) == CHOOSE x \in S : \A y \in S : y <= x
Min(S) == CHOOSE x \in S : \A y \in S : x <= y

\* 3. Generalized set reduction (fold over a set with an accumulator)
RECURSIVE SetFold(_,_ , _)
SetFold(S, acc, f) ==
  IF S = {} THEN acc
  ELSE
    LET a == CHOOSE x \in S IN
      SetFold(S \ {a}, f(acc, a), f)

\* 4. Sequence reduction (fold over a sequence with an accumulator)
RECURSIVE SeqFold(_,_ , _)
SeqFold(seq, acc, f) ==
  IF Len(seq) = 0 THEN acc
  ELSE SeqFold(Tail(seq), f(acc, Head(seq)), f)

\* 5. Finding the index of an element in a sequence (1‑based, 0 if absent)
IndexOf(seq, elem) ==
  IF elem ∉ SeqToSet(seq) THEN 0
  ELSE CHOOSE i \in 1..Len(seq) : seq[i] = elem

\* 6. Converting a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* 7. Getting the last element of a sequence
Last(seq) ==
  IF Len(seq) = 0 THEN <<>> \* undefined case returns empty sequence
  ELSE seq[Len(seq)]

\* 8. Testing if a sequence is empty
IsEmpty(seq) == Len(seq) = 0

\* 9. Removing all occurrences of an element from a sequence
RemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF Head(seq) = elem THEN RemoveAll(Tail(seq), elem)
  ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), elem)

\* 10. Computing the intersection of a set of sets
RECURSIVE SetIntersection(_)
SetIntersection(SS) ==
  IF SS = {} THEN {}
  ELSE
    LET S == CHOOSE s \in SS IN
      IF SS = {S} THEN S ELSE S \cap SetIntersection(SS \ {S})

\* 11. Generating all permutation sequences of a finite set
RECURSIVE Permutations(_)
Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE UNION { <<x>> \o p : x \in S, p \in Permutations(S \ {x}) }

\* 12. Test helper for assertions that print diagnostic information on failure
TestAssert(actual, expected, msg) ==
  IF actual = expected THEN TRUE
  ELSE (Print(msg, " expected=", expected, " actual=", actual); FALSE)

\* ----------------------------------------------------------------------
\* Trivial specification placeholders (required identifiers)
\* ----------------------------------------------------------------------
INIT == TRUE

NEXT == UNCHANGED <<>>

SPECIFICATION == INIT /\ [][NEXT]_<<>>

INVARIANTS == {}

PROPERTIES == {}

====