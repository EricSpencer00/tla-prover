---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\*  Set intersection test: returns TRUE iff the two sets overlap
\* ----------------------------------------------------------------------
SetOverlap(s, t) == s \cap t # {}

\* ----------------------------------------------------------------------
\*  Maximum and minimum element selection from a non‑empty finite set
\* ----------------------------------------------------------------------
MaxSet(s) == 
    IF s = {} THEN 
        (* Undefined for empty set; return a default value *) 
        0 
    ELSE 
        CHOOSE x \in s : \A y \in s : y <= x

MinSet(s) == 
    IF s = {} THEN 
        0 
    ELSE 
        CHOOSE x \in s : \A y \in s : y >= x

\* ----------------------------------------------------------------------
\*  Generalized set reduction (fold over a set with an accumulator)
\* ----------------------------------------------------------------------
SetReduce(s, f, acc) ==
    IF s = {} THEN 
        acc
    ELSE 
        LET e == CHOOSE x \in s IN
        SetReduce(s \ {e}, f, f(acc, e))

\* ----------------------------------------------------------------------
\*  Sequence reduction (fold over a sequence with an accumulator)
\* ----------------------------------------------------------------------
SeqReduce(seq, f, acc) ==
    IF Len(seq) = 0 THEN 
        acc
    ELSE 
        SeqReduce(Tail(seq), f, f(acc, Head(seq)))

\* ----------------------------------------------------------------------
\*  Find the index (1‑based) of the first occurrence of an element in a sequence;
\*  returns 0 if the element is not present
\* ----------------------------------------------------------------------
IndexOf(seq, elem) ==
    IF Len(seq) = 0 THEN 
        0
    ELSE IF Head(seq) = elem THEN 
        1
    ELSE 
        LET k == IndexOf(Tail(seq), elem) IN
        IF k = 0 THEN 0 ELSE k + 1

\* ----------------------------------------------------------------------
\*  Convert a sequence to the set of its elements
\* ----------------------------------------------------------------------
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* ----------------------------------------------------------------------
\*  Get the last element of a sequence (undefined for empty sequence)
\* ----------------------------------------------------------------------
Last(seq) ==
    IF Len(seq) = 0 THEN 
        (* undefined; return a default value *) 0
    ELSE 
        seq[Len(seq)]

\* ----------------------------------------------------------------------
\*  Test whether a sequence is empty
\* ----------------------------------------------------------------------
IsEmpty(seq) == Len(seq) = 0

\* ----------------------------------------------------------------------
\*  Remove all occurrences of an element from a sequence
\* ----------------------------------------------------------------------
RemoveAll(seq, elem) ==
    IF Len(seq) = 0 THEN 
        <<>>
    ELSE 
        IF Head(seq) = elem THEN 
            RemoveAll(Tail(seq), elem)
        ELSE 
            <<Head(seq)>> \o RemoveAll(Tail(seq), elem)

\* ----------------------------------------------------------------------
\*  Intersection of a set of sets
\* ----------------------------------------------------------------------
IntersectSets(S) == \Inter S

\* ----------------------------------------------------------------------
\*  Generate all permutations of a finite set as a set of sequences
\* ----------------------------------------------------------------------
Permutations(s) ==
    IF s = {} THEN 
        { <<>> }
    ELSE 
        UNION { <<e>> \o p : e \in s, p \in Permutations(s \ {e}) }

\* ----------------------------------------------------------------------
\*  Test helper for assertions that prints diagnostic information on failure
\* ----------------------------------------------------------------------
TestHelper(cond) ==
    IF cond THEN 
        TRUE 
    ELSE 
        (Print("Assertion failed: ", cond) /\ FALSE)

\* ----------------------------------------------------------------------
\*  Trivial specification placeholders required by the configuration
\* ----------------------------------------------------------------------
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====