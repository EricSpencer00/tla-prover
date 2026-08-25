---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\* Utility operators
\* ----------------------------------------------------------------------

\* 1. Set intersection test (whether two sets overlap)
Overlaps(S, T) == ~ (S \cap T = {})

\* 2. Maximum and minimum element selection from a set (assumes numeric elements)
MaxSet(S) == 
    IF S = {} THEN NULL
    ELSE CHOOSE x \in S : \A y \in S : x >= y

MinSet(S) == 
    IF S = {} THEN NULL
    ELSE CHOOSE x \in S : \A y \in S : x <= y

\* 3. Generalized set reduction (fold over a set with an accumulator)
\*    F is a binary operator, acc is the initial accumulator, S is the set.
SetReduce(F, acc, S) ==
    IF S = {} THEN acc
    ELSE 
        LET x == CHOOSE e \in S : TRUE
        IN SetReduce(F, F(acc, x), S \ {x})

\* 4. Sequence reduction (fold over a sequence with an accumulator)
SeqReduce(F, acc, seq) ==
    IF Len(seq) = 0 THEN acc
    ELSE SeqReduce(F, F(acc, Head(seq)), Tail(seq))

\* 5. Finding the index of an element in a sequence (1‑based, 0 if not found)
SeqIndex(seq, elem) ==
    IF Len(seq) = 0 THEN 0
    ELSE IF Head(seq) = elem THEN 1
    ELSE
        LET idx == SeqIndex(Tail(seq), elem)
        IN IF idx = 0 THEN 0 ELSE idx + 1

\* 6. Converting a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* 7. Getting the last element of a sequence (NULL if empty)
Last(seq) ==
    IF Len(seq) = 0 THEN NULL
    ELSE seq[Len(seq)]

\* 8. Testing if a sequence is empty
IsEmpty(seq) == Len(seq) = 0

\* 9. Removing all occurrences of an element from a sequence
RemoveAll(seq, elem) ==
    IF Len(seq) = 0 THEN <<>>
    ELSE
        IF Head(seq) = elem
        THEN RemoveAll(Tail(seq), elem)
        ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), elem)

\* 10. Computing the intersection of a set of sets
SetIntersection(SS) ==
    IF SS = {} THEN {}
    ELSE
        LET S == CHOOSE s \in SS : TRUE
        IN S \cap SetIntersection(SS \ {S})

\* 11. Generating all permutation sequences of a finite set
Permutations(S) ==
    IF S = {} THEN { <<>> }
    ELSE
        UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

\* 12. Test helper for writing assertions that print diagnostic information
TestHelper(cond, msg) ==
    IF cond THEN TRUE
    ELSE (Print(msg); FALSE)

\* ----------------------------------------------------------------------
\* Specification scaffolding (no state, purely functional library)
\* ----------------------------------------------------------------------
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====