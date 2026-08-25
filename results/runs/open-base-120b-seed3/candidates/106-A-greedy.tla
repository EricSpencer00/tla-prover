---- MODULE Util ----
EXTENDS Naturals, Sequences, TLC

\* ----------------------------------------------------------------------
\* Utility operators
\* ----------------------------------------------------------------------

\* 1. Set intersection test (whether two sets overlap)
Overlaps(S, T) == (S \cap T) # {}

\* 2. Maximum element selection from a non‑empty finite set
MaxSet(S) == 
    IF S = {} THEN 
        (* undefined for empty set *) 
        CHOOSE x : FALSE 
    ELSE 
        CHOOSE x \in S : \A y \in S : y <= x

\* 3. Minimum element selection from a non‑empty finite set
MinSet(S) == 
    IF S = {} THEN 
        CHOOSE x : FALSE 
    ELSE 
        CHOOSE x \in S : \A y \in S : y >= x

\* 4. Generalized set reduction (fold over a set with an accumulator)
\*    f is a binary operator: f(acc, element) -> newAcc
SetReduce(S, init, f) ==
    IF S = {} THEN 
        init
    ELSE 
        LET e == CHOOSE x \in S : TRUE IN
        SetReduce(S \ {e}, f(init, e), f)

\* 5. Sequence reduction (fold over a sequence with an accumulator)
\*    Implemented via the standard library FoldSeq
SeqReduce(seq, init, f) == FoldSeq(seq, init, f)

\* 6. Finding the index of an element in a sequence (1‑based)
\*    Returns 0 if the element is not present
IndexOf(seq, elem) ==
    IF \E i \in 1..Len(seq) : seq[i] = elem THEN
        CHOOSE i \in 1..Len(seq) : seq[i] = elem
    ELSE
        0

\* 7. Converting a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* 8. Getting the last element of a sequence
\*    Returns NULL for the empty sequence
Last(seq) ==
    IF Len(seq) = 0 THEN
        NULL
    ELSE
        seq[Len(seq)]

\* 9. Testing if a sequence is empty
IsEmpty(seq) == Len(seq) = 0

\* 10. Removing all occurrences of an element from a sequence
RemoveAll(seq, elem) ==
    IF Len(seq) = 0 THEN
        <<>>
    ELSE IF Head(seq) = elem THEN
        RemoveAll(Tail(seq), elem)
    ELSE
        <<Head(seq)>> \o RemoveAll(Tail(seq), elem)

\* 11. Computing the intersection of a set of sets
SetIntersectionOfSetOfSets(SS) ==
    IF SS = {} THEN
        {}
    ELSE
        \cap SS

\* 12. Generating all permutation sequences of a finite set
Permutations(S) ==
    IF S = {} THEN
        { <<>> }
    ELSE
        UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

\* 13. Test helper for writing assertions that print diagnostic information on failure
TestHelper(expr, msg) ==
    IF expr THEN
        TRUE
    ELSE
        (Print(msg); FALSE)

\* ----------------------------------------------------------------------
\* Place‑holder specification identifiers required by the configuration
\* ----------------------------------------------------------------------
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====