---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\* Utility operators used throughout the KV-store specifications.
\* ----------------------------------------------------------------------

\* 1) Set intersection test: returns TRUE iff the two sets share at least one element.
SetOverlap(S, T) == S \cap T # {}

\* 2) Maximum and minimum element selection from a non‑empty finite set.
SetMaximum(S) == 
    IF S = {} THEN 0 
    ELSE CHOOSE x \in S : \A y \in S : y <= x

SetMinimum(S) == 
    IF S = {} THEN 0 
    ELSE CHOOSE x \in S : \A y \in S : x <= y

\* 3) Generalized set reduction (fold) using a binary accumulator function.
\*    Base case on the empty set yields the supplied base value.
\*    The order of folding is nondeterministic, but the result is well‑defined
\*    for associative and commutative functions (as used by callers).
SetFold(base, acc, S) ==
    IF S = {} THEN base
    ELSE
        LET x == CHOOSE e \in S : TRUE IN
        SetFold(acc(base, x), acc, S \ {x})

\* 4) Sequence reduction (fold) implemented via the library operator FoldSeq.
SeqFold(base, acc, seq) == FoldSeq(base, acc, seq)

\* 5) Index of an element in a sequence (1‑based). Returns 0 if the element is absent.
IndexOf(x, seq) ==
    IF \E i \in 1..Len(seq) : seq[i] = x
    THEN
        CHOOSE i \in 1..Len(seq) : seq[i] = x
    ELSE 0

\* 6) Convert a sequence to the set of its elements.
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* 7) Get the last element of a non‑empty sequence.
Last(seq) == 
    IF Len(seq) = 0 
    THEN 0 
    ELSE seq[Len(seq)]

\* 8) Test if a sequence is empty.
SeqIsEmpty(seq) == Len(seq) = 0

\* 9) Remove all occurrences of a given element from a sequence.
RemoveAll(x, seq) ==
    [i \in 1..Cardinality({ j \in 1..Len(seq) : seq[j] # x }) |-> 
        seq[ CHOOSE j \in 1..Len(seq) : seq[j] # x /\ 
               Cardinality({ k \in 1..j : seq[k] # x }) = i )]

\* 10) Intersection of a set of sets (for an empty collection returns {}).
SetOfSetsIntersection(SS) ==
    IF SS = {} THEN {}
    ELSE \bigcap SS

\* 11) Generate all permutations of a finite set.
PermutationsSet(S) ==
    IF S = {} THEN { << >> }
    ELSE
        UNION { << e >> \o p : e \in S, p \in PermutationsSet(S \ {e}) }

\* 12) Assertion helper: returns TRUE if the condition holds;
\*     otherwise prints a diagnostic string and returns FALSE.
Assert(condition, msg) ==
    condition \/ (Print(msg); FALSE)

\* ----------------------------------------------------------------------
\* The specification does not introduce any state; nevertheless we expose
\* the standard identifiers expected by the configuration.
\* ----------------------------------------------------------------------
Spec == TRUE
Init == TRUE
Next == TRUE
Invariant == TRUE
Property == TRUE

=============================================================================