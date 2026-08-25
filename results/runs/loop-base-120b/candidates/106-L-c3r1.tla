---- MODULE Util ----
EXTENDS Naturals, Sequences, TLC

\* ---------- Utility Operators ----------

\* 1. Set intersection test (whether two sets overlap)
Overlap(S, T) == \E x \in S : x \in T

\* 2. Maximum and minimum element selection from a set
Max(S) == IF S = {} THEN NULL
          ELSE CHOOSE x \in S : \A y \in S : y <= x

Min(S) == IF S = {} THEN NULL
          ELSE CHOOSE x \in S : \A y \in S : x <= y

\* 3. Generalized set reduction (fold over a set with an accumulator)
RECURSIVE SetFold(_, _, _)
SetFold(F, acc, S) ==
  IF S = {} THEN acc
  ELSE LET x == CHOOSE y \in S : TRUE
       IN SetFold(F, F(acc, x), S \ {x})

\* 4. Sequence reduction (fold over a sequence with an accumulator)
SeqFold(F, acc, seq) == Fold(F, acc, seq)

\* 5. Finding the index of an element in a sequence (returns -1 if not found)
RECURSIVE IndexOf(_, _)
IndexOf(seq, e) ==
  IF Len(seq) = 0 THEN -1
  ELSE IF seq[1] = e THEN 1
       ELSE LET i == IndexOf(Tail(seq), e)
            IN IF i = -1 THEN -1 ELSE i + 1

\* 6. Converting a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* 7. Getting the last element of a sequence
Last(seq) == IF Len(seq) = 0 THEN NULL ELSE seq[Len(seq)]

\* 8. Testing if a sequence is empty
IsEmpty(seq) == Len(seq) = 0

\* 9. Removing all occurrences of an element from a sequence
RECURSIVE RemoveAll(_, _)
RemoveAll(seq, e) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF seq[1] = e THEN RemoveAll(Tail(seq), e)
       ELSE <<seq[1]>> \o RemoveAll(Tail(seq), e)

\* 10. Computing the intersection of a set of sets
RECURSIVE SetIntersectionAll(_)
SetIntersectionAll(Sets) ==
  IF Sets = {} THEN {}
  ELSE LET S == CHOOSE s \in Sets : TRUE
       IN SetIntersectionAll(Sets \ {S}) \cap S

\* 11. Generating all permutation sequences of a finite set
RECURSIVE Permutations(_)
Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

\* 12. Test helper for writing assertions that print diagnostic information on failure
TestHelper(cond, msg) ==
  IF cond THEN TRUE
  ELSE Print(msg) /\ FALSE

\* ---------- Specification Skeleton (no state) ----------
SPECIFICATION == TRUE
INIT == TRUE
NEXT == UNCHANGED <<>>
INVARIANTS == {}
PROPERTIES == {}

====