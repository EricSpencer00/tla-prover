---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ------------------------------------------------------------
\* Set intersection test: true iff two sets have a non‑empty overlap
\* ------------------------------------------------------------
SetOverlap(S, T) == /\ S \in SUBSET Nat
                 /\ T \in SUBSET Nat
                 /\ (S \cap T) # {}

\* ------------------------------------------------------------
\* Maximum and minimum element selection from a non‑empty set
\* ------------------------------------------------------------
SetMax(S) == 
    CHOOSE x \in S : \A y \in S : y <= x

SetMin(S) == 
    CHOOSE x \in S : \A y \in S : x <= y

\* ------------------------------------------------------------
\* Generalized set reduction (fold over a set with an accumulator)
\* ------------------------------------------------------------
SetReduce(F, acc, S) == 
    IF S = {} THEN acc
    ELSE 
        LET e == CHOOSE x \in S IN
        SetReduce(F, F(acc, e), S \ {e})

\* ------------------------------------------------------------
\* Sequence reduction (fold over a sequence with an accumulator)
\* ------------------------------------------------------------
SeqReduce(F, acc, seq) == 
    IF Len(seq) = 0 THEN acc
    ELSE SeqReduce(F, F(acc, Head(seq)), Tail(seq))

\* ------------------------------------------------------------
\* Finding the index of an element in a sequence (1‑based, 0 if absent)
\* ------------------------------------------------------------
IndexOf(seq, elem) == 
    IF Len(seq) = 0 THEN 0
    ELSE IF Head(seq) = elem THEN 1
    ELSE 
        LET i == IndexOf(Tail(seq), elem) IN
        IF i = 0 THEN 0 ELSE i + 1

\* ------------------------------------------------------------
\* Converting a sequence to the set of its elements
\* ------------------------------------------------------------
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* ------------------------------------------------------------
\* Getting the last element of a sequence (undefined for empty seq)
\* ------------------------------------------------------------
Last(seq) == 
    IF Len(seq) = 0 THEN 
        (* undefined; return a default value *) 
        NULL
    ELSE seq[Len(seq)]

\* ------------------------------------------------------------
\* Testing if a sequence is empty
\* ------------------------------------------------------------
SeqIsEmpty(seq) == Len(seq) = 0

\* ------------------------------------------------------------
\* Removing all occurrences of an element from a sequence
\* ------------------------------------------------------------
RemoveAll(seq, elem) == 
    IF Len(seq) = 0 THEN <<>>
    ELSE 
        IF Head(seq) = elem THEN 
            RemoveAll(Tail(seq), elem)
        ELSE 
            <<Head(seq)>> \o RemoveAll(Tail(seq), elem)

\* ------------------------------------------------------------
\* Intersection of a set of sets (empty collection yields {} )
\* ------------------------------------------------------------
SetIntersection(SS) == 
    IF SS = {} THEN {}
    ELSE
        LET S0 == CHOOSE S \in SS IN
        S0 \cap SetIntersection(SS \ {S0})

\* ------------------------------------------------------------
\* Generating all permutations of a finite set
\* ------------------------------------------------------------
Permutations(S) == 
    IF S = {} THEN { <<>> }
    ELSE 
        UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

\* ------------------------------------------------------------
\* Test helper for assertions that prints diagnostic information on failure
\* ------------------------------------------------------------
Assert(cond, msg) == 
    IF cond THEN TRUE 
    ELSE (Print(msg); FALSE)

=============================================================================