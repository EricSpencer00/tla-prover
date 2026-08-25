---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

\* ------------------------------------------------------------
\* 1. Set overlap test
\* ------------------------------------------------------------
SetOverlap(S, T) == 
    \E x \in S : x \in T

\* ------------------------------------------------------------
\* 2. Maximum and minimum element selection from a set
\* ------------------------------------------------------------
SetMax(S) == 
    IF S = {} THEN {} 
    ELSE CHOOSE x \in S : \A y \in S : y <= x

SetMin(S) == 
    IF S = {} THEN {} 
    ELSE CHOOSE x \in S : \A y \in S : y >= x

\* ------------------------------------------------------------
\* 3. Generalized set reduction (fold over a set)
\* ------------------------------------------------------------
SetReduce(S, op, acc) == 
    IF S = {} THEN acc
    ELSE 
        LET e == CHOOSE x \in S : TRUE
        IN SetReduce(S \ {e}, op, op[acc, e])

\* ------------------------------------------------------------
\* 4. Sequence reduction (fold over a sequence)
\* ------------------------------------------------------------
SeqReduce(seq, op, acc) == 
    IF Len(seq) = 0 THEN acc
    ELSE SeqReduce(Tail(seq), op, op[acc, Head(seq)])

\* ------------------------------------------------------------
\* Helper operators for sequences
\* ------------------------------------------------------------
Head(seq) == seq[1]

Tail(seq) == 
    [i \in 1..(Len(seq)-1) |-> seq[i+1]]

\* ------------------------------------------------------------
\* 5. Finding the index of an element in a sequence
\* ------------------------------------------------------------
SeqIndex(seq, elem) == 
    IF elem \in SeqToSet(seq) THEN
        CHOOSE i \in 1..Len(seq) : seq[i] = elem
    ELSE
        0

\* ------------------------------------------------------------
\* 6. Converting a sequence to the set of its elements
\* ------------------------------------------------------------
SeqToSet(seq) == { seq[i] : i \in DOMAIN seq }

\* ------------------------------------------------------------
\* 7. Getting the last element of a sequence
\* ------------------------------------------------------------
Last(seq) == 
    IF Len(seq) = 0 THEN {} 
    ELSE seq[Len(seq)]

\* ------------------------------------------------------------
\* 8. Testing if a sequence is empty
\* ------------------------------------------------------------
SeqIsEmpty(seq) == Len(seq) = 0

\* ------------------------------------------------------------
\* 9. Removing all occurrences of an element from a sequence
\* ------------------------------------------------------------
SeqRemoveAll(seq, elem) == 
    IF Len(seq) = 0 THEN <<>>
    ELSE 
        LET rest == SeqRemoveAll(Tail(seq), elem)
        IN IF Head(seq) = elem THEN rest ELSE <<Head(seq)>> \o rest

\* ------------------------------------------------------------
\* 10. Intersection of a set of sets
\* ------------------------------------------------------------
SetIntersection(SS) == 
    IF SS = {} THEN {} 
    ELSE INTERSECTION(SS)

\* ------------------------------------------------------------
\* 11. Generating all permutation sequences of a finite set
\* ------------------------------------------------------------
Permutations(S) == 
    IF S = {} THEN { <<>> }
    ELSE UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

\* ------------------------------------------------------------
\* 12. Test helper for assertions with diagnostic output
\* ------------------------------------------------------------
TestHelper(expr, msg) == 
    IF expr THEN TRUE 
    ELSE (Print(msg); FALSE)

====