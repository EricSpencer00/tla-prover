---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ------------------------------
\* Set intersection test (whether two sets overlap)
\* ------------------------------
SetOverlap(A, B) == (A \cap B) /= {}

\* ------------------------------
\* Maximum and minimum element selection from a non‑empty finite set
\* ------------------------------
MaxElement(S) ==
    IF S = {} THEN
        NULL
    ELSE
        CHOOSE x \in S : \A y \in S : y <= x

MinElement(S) ==
    IF S = {} THEN
        NULL
    ELSE
        CHOOSE x \in S : \A y \in S : y >= x

\* ------------------------------
\* Generalized set reduction (fold over a set with an accumulator)
\* ------------------------------
SetReduce(S, acc, f) ==
    IF S = {} THEN
        acc
    ELSE
        LET e == CHOOSE x \in S : TRUE
        IN SetReduce(S \ {e}, f(acc, e), f)

\* ------------------------------
\* Sequence reduction (fold over a sequence with an accumulator)
\* ------------------------------
Head(s) == s[1]

Tail(s) ==
    IF Len(s) <= 1 THEN
        <<>>
    ELSE
        SubSeq(s, 2, Len(s))

SeqReduce(s, acc, f) ==
    IF Len(s) = 0 THEN
        acc
    ELSE
        SeqReduce(Tail(s), f(acc, Head(s)), f)

\* ------------------------------
\* Finding the index of an element in a sequence (0 if not present)
\* ------------------------------
IndexOf(s, e) ==
    IF Len(s) = 0 THEN
        0
    ELSE
        IF Head(s) = e THEN
            1
        ELSE
            LET r == IndexOf(Tail(s), e)
            IN IF r = 0 THEN 0 ELSE 1 + r

\* ------------------------------
\* Converting a sequence to the set of its elements
\* ------------------------------
SeqToSet(s) == { s[i] : i \in 1 .. Len(s) }

\* ------------------------------
\* Getting the last element of a sequence (NULL if empty)
\* ------------------------------
Last(s) ==
    IF Len(s) = 0 THEN
        NULL
    ELSE
        s[Len(s)]

\* ------------------------------
\* Testing if a sequence is empty
\* ------------------------------
IsEmpty(s) == Len(s) = 0

\* ------------------------------
\* Removing all occurrences of an element from a sequence
\* ------------------------------
RemoveAll(s, e) ==
    IF Len(s) = 0 THEN
        <<>>
    ELSE
        IF Head(s) = e THEN
            RemoveAll(Tail(s), e)
        ELSE
            <<Head(s)>> \o RemoveAll(Tail(s), e)

\* ------------------------------
\* Computing the intersection of a set of sets
\* ------------------------------
IntersectionOfSets(SS) ==
    IF SS = {} THEN
        {}
    ELSE
        LET S0 == CHOOSE s \in SS : TRUE
        IN IF SS = {S0} THEN
               S0
           ELSE
               S0 \cap IntersectionOfSets(SS \ {S0})

\* ------------------------------
\* Generating all permutation sequences of a finite set
\* ------------------------------
Permutations(S) ==
    IF S = {} THEN
        { <<>> }
    ELSE
        UNION { { <<e>> \o p } : e \in S, p \in Permutations(S \ {e}) }

\* ------------------------------
\* Test helper for writing assertions that print diagnostic information on failure
\* ------------------------------
TestHelper(cond, msg) ==
    IF cond THEN
        TRUE
    ELSE
        Print(msg) /\ FALSE

====