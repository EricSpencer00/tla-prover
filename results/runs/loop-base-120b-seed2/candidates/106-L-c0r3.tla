---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Utility operators
\* ----------------------------------------------------------------------

\* 1. Set intersection test (whether two sets overlap)
SetOverlap(S, T) == (S \cap T) # {}

\* 2. Maximum element selection from a non‑empty finite set
SetMax(S) ==
    CHOOSE x \in S : \A y \in S : y <= x

\* 3. Minimum element selection from a non‑empty finite set
SetMin(S) ==
    CHOOSE x \in S : \A y \in S : x <= y

\* 4. Generalized set reduction (fold over a set with an accumulator)
RECURSIVE SetReduce(_,_,_)
SetReduce(S, init, f) ==
    IF S = {} THEN init
    ELSE LET e == CHOOSE x \in S : TRUE IN
         SetReduce(S \ {e}, f(init, e), f)

\* 5. Sequence reduction (fold over a sequence with an accumulator)
RECURSIVE SeqReduce(_,_,_)
SeqReduce(seq, init, f) ==
    IF Len(seq) = 0 THEN init
    ELSE SeqReduce(SubSeq(seq, 2, Len(seq)), f(init, seq[1]), f)

\* 6. Finding the index of an element in a sequence (1‑based, 0 if absent)
RECURSIVE SeqIndex(_,_)
SeqIndex(seq, elem) ==
    IF Len(seq) = 0 THEN 0
    ELSE IF seq[1] = elem THEN 1
    ELSE LET i == SeqIndex(SubSeq(seq, 2, Len(seq)), elem) IN
         IF i = 0 THEN 0 ELSE i + 1

\* 7. Converting a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* 8. Getting the last element of a sequence (NULL if empty)
SeqLast(seq) == IF Len(seq) = 0 THEN NULL ELSE seq[Len(seq)]

\* 9. Testing if a sequence is empty
SeqIsEmpty(seq) == Len(seq) = 0

\* 10. Removing all occurrences of an element from a sequence
RECURSIVE SeqRemoveAll(_,_)
SeqRemoveAll(seq, elem) ==
    IF Len(seq) = 0 THEN <<>>
    ELSE IF seq[1] = elem THEN
         SeqRemoveAll(SubSeq(seq, 2, Len(seq)), elem)
    ELSE
         (<< seq[1] >>) ^ SeqRemoveAll(SubSeq(seq, 2, Len(seq)), elem)

\* 11. Computing the intersection of a set of sets
SetIntersection(S) == INTERSECTION S

\* 12. Generating all permutation sequences of a finite set
RECURSIVE Permutations(_)
Permutations(S) ==
    IF S = {} THEN { << >> }
    ELSE UNION { (<< e >>) ^ p : e \in S, p \in Permutations(S \ {e}) }

\* 13. Test helper for writing assertions that print diagnostic information
TestHelper(expr, msg) ==
    IF expr THEN TRUE ELSE (Print(msg) /\ FALSE)

\* ----------------------------------------------------------------------
\* Trivial specification skeleton (required identifiers)
\* ----------------------------------------------------------------------
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====