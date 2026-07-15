---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\* Utility operators for use by other modules
\* ----------------------------------------------------------------------


\*----------------------------------------------------------------------
\* 1. Set intersection test: Overlap(s, t) is TRUE iff s and t share at least one
\*    element.
\*----------------------------------------------------------------------
Overlap(s, t) == \E x \in s : x \in t


\*----------------------------------------------------------------------
\* 2. Maximum and minimum element selection from a non‑empty set.
\*----------------------------------------------------------------------
Max(s) == 
    IF s = {} THEN 0
    ELSE CHOOSE x \in s : \A y \in s : y <= x

Min(s) == 
    IF s = {} THEN 0
    ELSE CHOOSE x \in s : \A y \in s : x <= y


\*----------------------------------------------------------------------
\* 3. Generalized set reduction (fold over a set with an accumulator).
\*    SetReduce(f, a, S) applies binary operator f left‑associatively to the
\*    elements of S starting with accumulator a.
\*----------------------------------------------------------------------
SetReduce(f, a, S) ==
    IF S = {} THEN a
    ELSE LET x == CHOOSE y \in S : TRUE
         IN SetReduce(f, f(a, x), S \ {x})


\*----------------------------------------------------------------------
\* 4. Sequence reduction using the library FoldSeq operator.
\*----------------------------------------------------------------------
SeqReduce(f, a, seq) == FoldSeq(f, a, seq)


\*----------------------------------------------------------------------
\* 5. Index of an element in a sequence (first occurrence, 1‑based).
\*----------------------------------------------------------------------
IndexOf(seq, e) ==
    IF e \notin SeqToSet(seq) THEN 0
    ELSE
        LET pos == CHOOSE i \in DOMAIN seq :
                       seq[i] = e
        IN pos


\*----------------------------------------------------------------------
\* 6. Convert a sequence to the set of its elements.
\*----------------------------------------------------------------------
SeqToSet(seq) == { seq[i] : i \in DOMAIN seq }


\*----------------------------------------------------------------------
\* 7. The last element of a non‑empty sequence.
\*----------------------------------------------------------------------
Last(seq) == seq[ Len(seq) ]


\*----------------------------------------------------------------------
\* 8. Test if a sequence is empty.
\*----------------------------------------------------------------------
IsEmpty(seq) == Len(seq) = 0


\*----------------------------------------------------------------------
\* 9. Remove all occurrences of an element from a sequence.
\*----------------------------------------------------------------------
RemoveAll(seq, e) ==
    [ i \in 1..( Len(seq) - Cardinality({ j \in DOMAIN seq : seq[j] = e })) |
        LET filtered == { j \in DOMAIN seq : seq[j] # e } IN
        LET sorted == SeqSort(SeqFromSet(filtered)) IN
        seq[ sorted[i] ] ]


\*----------------------------------------------------------------------
\* 10. Intersection of a set of sets.
\*----------------------------------------------------------------------
SetIntersection(SS) ==
    IF SS = {} THEN {}
    ELSE \A x \in SS : x


\*----------------------------------------------------------------------
\* 11. Generate all permutations of a finite set.
\*----------------------------------------------------------------------
Permutations(s) ==
    IF s = {} THEN { << >> }
    ELSE
        UNION { 
            << e >> \o p :
                e \in s /\ 
                p \in Permutations(s \ {e})
        }


\*----------------------------------------------------------------------
\* 12. Test helper that prints a message when a condition fails.
\*----------------------------------------------------------------------
TestAssert(cond, msg) ==
    IF cond THEN TRUE
    ELSE
        Print("Test assertion failed: " ^ msg);
        FALSE


\*----------------------------------------------------------------------
\* 13. A trivial TLC configuration – required identifiers.
\*----------------------------------------------------------------------
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

=============================================================================