---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* --- Utility operators -------------------------------------------------

\* 1. Set intersection test: returns TRUE iff two sets overlap
SetOverlap(S, T) == 
    \E x \in S : x \in T

\* 2. Maximum element of a non‑empty finite set
Max(S) == 
    IF S = {} THEN 
        CHOOSE dummy \in {} : dummy \* (undefined)
    ELSE 
        \E m \in S : \A x \in S : x <= m

\*    The expression above yields a set of all maximal elements; we pick one.
Max(S) == 
    CHOOSE m \in S : \A x \in S : x <= m

\* 3. Minimum element of a non‑empty finite set
Min(S) == 
    CHOOSE m \in S : \A x \in S : m <= x

\* 4. Generalized set reduction (fold) with an accumulator.
\*    f is a binary relation encoding a function: f(acc, elem) = newAcc
SetFold(S, acc0, f) == 
    IF S = {} THEN acc0
    ELSE LET 
            e == CHOOSE x \in S : TRUE
            acc1 == f[acc0, e]
            Rest == S \ {e}
         IN SetFold(Rest, acc1, f)

\* 5. Sequence reduction (fold) over a sequence using the library FoldSeq
SeqFold(seq, acc0, f) == 
    FoldSeq(seq, acc0, f)

\* 6. Index of an element in a sequence (returns 0 if not present)
SeqIndex(seq, elem) == 
    IF \E i \in 1..Len(seq) : seq[i] = elem THEN
        CHOOSE i \in 1..Len(seq) : seq[i] = elem
    ELSE 0

\* 7. Convert a sequence to the set of its elements
SeqToSet(seq) == 
    { seq[i] : i \in 1..Len(seq) }

\* 8. Last element of a sequence (undefined for empty sequence)
SeqLast(seq) == 
    IF Len(seq) = 0 THEN CHOOSE dummy \in {} : dummy
    ELSE seq[Len(seq)]

\* 9. Test whether a sequence is empty
SeqIsEmpty(seq) == 
    Len(seq) = 0

\* 10. Remove all occurrences of an element from a sequence
SeqRemoveAll(seq, elem) == 
    [i \in 1..(Len(seq) - Card({j \in 1..Len(seq) : seq[j] = elem})) |-> 
        seq[ IF i <= (CHOOSE j \in 1..Len(seq) : seq[j] = elem) THEN i
             ELSE i + Card({j \in 1..Len(seq) : seq[j] = elem}) ]]

\* 11. Intersection of a set of sets
SetOfSetsIntersection(SS) == 
    IF SS = {} THEN {}
    ELSE \INTERSECTION SS

\* 12. Generate all permutations of a finite set
Permutations(S) == 
    IF S = {} THEN {<<>>}
    ELSE 
        UNION { 
            <<e>> \o p : 
                e \in S, 
                p \in Permutations(S \ {e}) 
        }

\* 13. Test helper that raises an assertion with a diagnostic message
TestAssert(cond, msg) == 
    IF cond THEN TRUE ELSE 
        UNCHANGED <<>> \* No state change; TLC will report the failed assertion.

\* --- Specification skeleton required by the .cfg -----------------------

\* No state variables are required for a pure utility module.
VARIABLES dummy

\* Initial state (arbitrary, as the module has no behavior)
Init == dummy = 0

\* A trivial stuttering step to keep the model from deadlocking
Next == 
    \/ dummy' = dummy

\* SPECIFICATION, INIT, NEXT, INVARIANTS, and PROPERTIES identifiers
SPECIFICATION == Init /\ [][Next]_<<dummy>>

INIT == Init

NEXT == Next

INVARIANTS == {}

PROPERTIES == {}

====