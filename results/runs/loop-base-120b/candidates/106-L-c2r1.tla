---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\* Utility operators
\* ----------------------------------------------------------------------

\* 1. Set intersection test (whether two sets overlap)
Overlap(S, T) == (S \cap T) # {}

\* 2. Maximum and minimum element selection from a set
SetMax(S) == 
    CHOOSE x \in S : \A y \in S : y <= x

SetMin(S) == 
    CHOOSE x \in S : \A y \in S : x <= y

\* 3. Generalized set reduction (fold over a set with an accumulator)
RECURSIVE SetFold(_, _, _)
SetFold(S, init, op) ==
    IF S = {} THEN init
    ELSE 
        LET x == CHOOSE e \in S : TRUE IN
        SetFold(S \ {x}, op(init, x), op)

\* 4. Sequence reduction (fold over a sequence with an accumulator)
RECURSIVE SeqFold(_, _, _)
SeqFold(seq, init, op) ==
    IF Len(seq) = 0 THEN init
    ELSE SeqFold(Tail(seq), op(init, Head(seq)), op)

\* 5. Finding the index of an element in a sequence (1‑based, 0 if not found)
RECURSIVE IndexOf(_, _)
IndexOf(seq, elem) ==
    IF Len(seq) = 0 THEN 0
    ELSE IF Head(seq) = elem THEN 1
    ELSE 
        LET i == IndexOf(Tail(seq), elem) IN
        IF i = 0 THEN 0 ELSE i + 1

\* 6. Converting a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* 7. Getting the last element of a sequence
Last(seq) ==
    IF Len(seq) = 0 THEN
        CHOOSE x \in {} : FALSE  \* undefined for empty sequence
    ELSE seq[Len(seq)]

\* 8. Testing if a sequence is empty
SeqIsEmpty(seq) == Len(seq) = 0

\* 9. Removing all occurrences of an element from a sequence
RECURSIVE RemoveAll(_, _)
RemoveAll(seq, elem) ==
    IF Len(seq) = 0 THEN <<>>
    ELSE IF Head(seq) = elem THEN
        RemoveAll(Tail(seq), elem)
    ELSE
        <<Head(seq)>> \o RemoveAll(Tail(seq), elem)

\* 10. Computing the intersection of a set of sets
RECURSIVE SetIntersection(_)
SetIntersection(SS) ==
    IF SS = {} THEN {}
    ELSE 
        LET s == CHOOSE t \in SS : TRUE IN
        s \cap SetIntersection(SS \ {s})

\* 11. Generating all permutation sequences of a finite set
RECURSIVE Permutations(_)
Permutations(S) ==
    IF S = {} THEN { <<>> }
    ELSE UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

\* 12. Test helper for assertions with diagnostic output
TestAssert(cond, msg) ==
    IF cond THEN TRUE
    ELSE (Print(msg); FALSE)

\* ----------------------------------------------------------------------
\* Stubs required by the .cfg (no state, so everything is true)
\* ----------------------------------------------------------------------
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

=============================================================================