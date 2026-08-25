---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* 1. Set intersection test (whether two sets overlap)
\* ----------------------------------------------------------------------
SetOverlap(S, T) == (S \cap T) # {}

\* ----------------------------------------------------------------------
\* 2. Maximum and minimum element selection from a set (assumes total order)
\* ----------------------------------------------------------------------
Max(S) == 
    IF S = {} THEN 
        CHOOSE x : FALSE \* undefined for empty set
    ELSE 
        CHOOSE x \in S : \A y \in S : y <= x

Min(S) == 
    IF S = {} THEN 
        CHOOSE x : FALSE \* undefined for empty set
    ELSE 
        CHOOSE x \in S : \A y \in S : x <= y

\* ----------------------------------------------------------------------
\* 3. Generalized set reduction (fold over a set with an accumulator)
\* ----------------------------------------------------------------------
RECURSIVE SetFold(_,_ ,_)
SetFold(S, init, f) ==
    IF S = {} THEN 
        init
    ELSE 
        LET e == CHOOSE x \in S : TRUE IN
        SetFold(S \ {e}, f(e, init), f)

\* ----------------------------------------------------------------------
\* 4. Sequence reduction (fold over a sequence with an accumulator)
\* ----------------------------------------------------------------------
RECURSIVE SeqFold(_,_ ,_)
SeqFold(seq, init, f) ==
    IF Len(seq) = 0 THEN 
        init
    ELSE 
        f(Head(seq), SeqFold(Tail(seq), init, f))

\* ----------------------------------------------------------------------
\* 5. Finding the index of an element in a sequence (first occurrence)
\* ----------------------------------------------------------------------
SeqIndex(seq, elem) ==
    IF \E i \in 1..Len(seq) : seq[i] = elem THEN
        CHOOSE i \in 1..Len(seq) : seq[i] = elem
    ELSE
        0 \* 0 denotes “not found”

\* ----------------------------------------------------------------------
\* 6. Converting a sequence to the set of its elements
\* ----------------------------------------------------------------------
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* ----------------------------------------------------------------------
\* 7. Getting the last element of a sequence
\* ----------------------------------------------------------------------
Last(seq) ==
    IF Len(seq) = 0 THEN
        NULL
    ELSE
        seq[Len(seq)]

\* ----------------------------------------------------------------------
\* 8. Testing if a sequence is empty
\* ----------------------------------------------------------------------
SeqIsEmpty(seq) == Len(seq) = 0

\* ----------------------------------------------------------------------
\* 9. Removing all occurrences of an element from a sequence
\* ----------------------------------------------------------------------
SeqRemove(seq, elem) == 
    [ seq[i] : i \in 1..Len(seq) \ /\ seq[i] # elem ]

\* ----------------------------------------------------------------------
\* 10. Computing the intersection of a set of sets
\* ----------------------------------------------------------------------
SetIntersection(SS) ==
    IF SS = {} THEN {} ELSE \cap SS

\* ----------------------------------------------------------------------
\* 11. Generating all permutation sequences of a finite set
\* ----------------------------------------------------------------------
RECURSIVE Permutations(_)
Permutations(S) ==
    IF S = {} THEN
        { << >> }
    ELSE
        UNION { << e >> \o p :
                e \in S,
                p \in Permutations(S \ {e}) }

\* ----------------------------------------------------------------------
\* 12. Test helper for writing assertions that print diagnostic information
\* ----------------------------------------------------------------------
Assert(cond, msg) ==
    IF cond THEN TRUE
    ELSE (Print(msg); FALSE)

=============================================================================