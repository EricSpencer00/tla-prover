---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* -------------------------------------------------
\* Utility operators
\* -------------------------------------------------

\* (1) Set intersection test: returns TRUE iff two sets overlap
SetOverlap(S, T) == \E x \in S : x \in T

\* (2) Maximum and minimum element selection from a non‑empty set
SetMax(S) == 
    IF S = {} THEN 
        CHOOSE x : FALSE \* undefined for empty set
    ELSE 
        LET m == CHOOSE x \in S : \A y \in S : y <= x 
        IN m

SetMin(S) == 
    IF S = {} THEN 
        CHOOSE x : FALSE \* undefined for empty set
    ELSE 
        LET m == CHOOSE x \in S : \A y \in S : y >= x 
        IN m

\* (3) Generalized set reduction (fold over a set with an accumulator)
\* f is a binary operator: f(acc, element) returns the new accumulator
SetFold(S, acc, f) == 
    IF S = {} THEN 
        acc
    ELSE 
        LET e == CHOOSE x \in S 
        IN SetFold(S \ {e}, f(acc, e), f)

\* (4) Sequence reduction (fold over a sequence with an accumulator)
\* implemented via a recursive definition
SeqFold(seq, acc, f) == 
    IF Len(seq) = 0 THEN 
        acc
    ELSE 
        SeqFold(SeqTail(seq), f(acc, SeqHead(seq)), f)

\* Helper to obtain the tail of a sequence
SeqTail(seq) == 
    IF Len(seq) <= 1 THEN <<>> 
    ELSE SubSeq(seq, 2, Len(seq))

\* (5) Finding the index of an element in a sequence (1‑based, 0 if absent)
IndexOf(seq, elem) == 
    IF elem \in SeqToSet(seq) THEN 
        CHOOSE i \in 1..Len(seq) : seq[i] = elem
    ELSE 
        0

\* (6) Converting a sequence to the set of its elements
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* (7) Getting the last element of a sequence (NULL if empty)
Last(seq) == 
    IF Len(seq) = 0 THEN NULL 
    ELSE seq[Len(seq)]

\* (8) Testing if a sequence is empty
IsEmpty(seq) == Len(seq) = 0

\* (9) Removing all occurrences of an element from a sequence
RemoveAll(seq, elem) == 
    IF Len(seq) = 0 THEN 
        <<>>
    ELSE 
        IF seq[1] = elem THEN 
            RemoveAll(SeqTail(seq), elem)
        ELSE 
            <<seq[1]>> \o RemoveAll(SeqTail(seq), elem)

\* (10) Computing the intersection of a set of sets
SetIntersection(SS) == 
    IF SS = {} THEN 
        {} 
    ELSE 
        { x \in UNION SS : \A Y \in SS : x \in Y }

\* (11) Generating all permutation sequences of a finite set
Permutations(S) == 
    IF S = {} THEN 
        { <<>> } 
    ELSE 
        UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

\* (12) Test helper for writing assertions that print diagnostic information on failure
TestHelper(msg, cond) == 
    IF cond THEN 
        TRUE 
    ELSE 
        Print(msg) /\ FALSE

\* -------------------------------------------------
\* Trivial specification skeleton required by the task
\* -------------------------------------------------
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====