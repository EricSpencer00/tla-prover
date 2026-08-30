---- MODULE Util ----
EXTENDS Sequences, Integers

CONSTANTS MaxElement

\* Utility: return any element of the set (non-deterministically chosen).
PickOne(S) == CHOOSE x \in S : TRUE

\* 1. Intersection: do two sets overlap?
SetIntersect(A, B) == \E x \in A : x \in B

\* 2. Max and min element of a non-empty set (bounded by MaxElement).
SetMax(S) == CHOOSE x \in S : \A y \in S : y <= x
SetMin(S) == CHOOSE x \in S : \A y \in S : y >= x

\* 3. Generic set reduction: fold over a set with an accumulator.
SetFold(f, S, a) ==
  IF S = {} THEN a
  ELSE SetFold(f, S \ {PickOne(S)}, f(PickOne(S), a)

\* 4. Sequence reduction (fold over a sequence); uses the library's FoldSeq.
SeqFold(f, s, a) == FoldSeq(f, s, a)

\* 5. Index of an element in a sequence; -1 if not present.
SeqIndex(s, e) ==
  LET Scan(i) == IF i > Len(s) THEN -1
                 ELSE IF s[i] = e THEN i
                 ELSE Scan(i + 1)
  IN Scan(1)

\* 6. Convert a sequence to the set of its elements.
SeqAsSet(s) == { s[i] : i \in 1..Len(s) }

\* 7. The last element of a non-empty sequence.
LastOf(s) == s[Len(s)]

\* 8. Test whether a sequence is empty.
SeqEmpty(s) == Len(s) = 0

\* 9. Remove all occurrences of an element from a sequence.
SeqRemoveAll(s, e) == FilterSeq(s, LAMBDA x : x # e)

\* 10. Intersection of a set of sets.
IntersectionOfSets(S) ==
  IF S = {} THEN {}
  ELSE SetFold(SetIntersect, S, PickOne(S))

\* 11. Generate all permutation sequences of a finite set.
PermutationsOf(S) ==
  IF S = {} THEN { << >> }
  ELSE { << x >> \o p : x \in S, p \in PermutationsOf(S \ {x}) }

\* 12. Test helper: assert a condition, printing a message on failure.
TestAssert(cond, msg) == IF cond THEN "ok" ELSE Print(msg)

====