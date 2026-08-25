---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* 1. Set intersection test (whether two sets overlap)
SetOverlap(S, T) == (S \cap T) # {}

\* 2. Maximum element selection from a set (assumes a total order, e.g., numbers)
SetMax(S) == CHOOSE x \in S: \A y \in S: y <= x

\* 2. Minimum element selection from a set
SetMin(S) == CHOOSE x \in S: \A y \in S: x <= y

\* 3. Generalized set reduction (fold over a set with an accumulator)
SetReduce(S, acc, f) ==
    IF S = {} THEN acc
    ELSE
        LET e == CHOOSE x \in S: TRUE
        IN SetReduce(S \ {e}, f(acc, e), f)

\* 4. Sequence reduction (fold over a sequence with an accumulator)
SeqReduce(seq, acc, f) ==
    IF Len(seq) = 0 THEN acc
    ELSE SeqReduce(Tail(seq), f(acc, Head(seq)), f)

\* 5. Finding the index of an element in a sequence (1‑based, 0 if not present)
SeqIndex(seq, elem) ==
    IF Len(seq) = 0 THEN 0
    ELSE IF Head(seq) = elem THEN 1
    ELSE
        LET idx == SeqIndex(Tail(seq), elem) IN
            IF idx = 0 THEN 0 ELSE idx + 1

\* 6. Converting a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* 7. Getting the last element of a sequence (requires non‑empty sequence)
SeqLast(seq) == seq[Len(seq)]

\* 8. Testing if a sequence is empty
SeqIsEmpty(seq) == Len(seq) = 0

\* 9. Removing all occurrences of an element from a sequence
SeqRemoveAll(seq, elem) ==
    IF Len(seq) = 0 THEN <<>>
    ELSE IF Head(seq) = elem THEN SeqRemoveAll(Tail(seq), elem)
    ELSE <<Head(seq)>> \o SeqRemoveAll(Tail(seq), elem)

\* 10. Computing the intersection of a set of sets
SetIntersection(SS) == IF SS = {} THEN {} ELSE \cap SS

\* 11. Generating all permutation sequences of a finite set
SetPermutations(S) ==
    IF S = {} THEN { <<>> }
    ELSE { <<e>> \o p : e \in S, p \in SetPermutations(S \ {e}) }

\* 12. Test helper for assertions that prints diagnostic information on failure
TestHelper(expr, msg) ==
    IF expr THEN TRUE ELSE (Print(msg); FALSE)

====