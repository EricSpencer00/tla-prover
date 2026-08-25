---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

\* 1. Set intersection test (whether two sets overlap)
SetOverlap(S, T) == \E x \in S : x \in T

\* 2. Maximum and minimum element selection from a set (assumes non‑empty, totally ordered)
SetMax(S) == 
  CHOOSE m \in S : \A x \in S : x <= m

SetMin(S) == 
  CHOOSE m \in S : \A x \in S : m <= x

\* 3. Generalized set reduction (fold over a set with an accumulator)
SetFold(S, acc, f) ==
  IF S = {} THEN acc
  ELSE 
    LET x == CHOOSE y \in S : TRUE
    IN SetFold(S \ {x}, f(acc, x), f)

\* 4. Sequence reduction (fold over a sequence with an accumulator)
SeqFold(seq, acc, f) ==
  IF Len(seq) = 0 THEN acc
  ELSE SeqFold(Tail(seq), f(acc, Head(seq)), f)

\* 5. Finding the index of an element in a sequence (0 if not present)
IndexOf(seq, elem) ==
  IF Len(seq) = 0 THEN 0
  ELSE IF Head(seq) = elem THEN 1
       ELSE 
         LET i == IndexOf(Tail(seq), elem)
         IN IF i = 0 THEN 0 ELSE i + 1

\* 6. Converting a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* 7. Getting the last element of a sequence (NULL if empty)
Last(seq) == IF Len(seq) = 0 THEN NULL ELSE seq[Len(seq)]

\* 8. Testing if a sequence is empty
IsEmpty(seq) == Len(seq) = 0

\* 9. Removing all occurrences of an element from a sequence
RemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF Head(seq) = elem THEN RemoveAll(Tail(seq), elem)
       ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), elem)

\* 10. Computing the intersection of a set of sets
IntersectAll(SS) ==
  IF SS = {} THEN {}
  ELSE 
    LET S0 == CHOOSE s \in SS : TRUE
    IN S0 \cap IntersectAll(SS \ {S0})

\* 11. Generating all permutation sequences of a finite set
Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE 
    UNION { <<x>> \o p : x \in S, p \in Permutations(S \ {x}) }

\* 12. Test helper for assertions that print diagnostic information on failure
TestHelper(cond, msg) ==
  IF cond THEN TRUE
  ELSE Print(msg) /\ FALSE

====