---- MODULE Util ----
EXTENDS Naturals, Sequences

CONSTANTS MaxVal

\* set intersection test: true iff the two sets have at least one element in common
Intersects(S, T) == Cardinality(S \cap T) > 0

\* extremal element selection from a nonempty set
\* (these are partial, defined only when S is nonempty)
MaxOf(S) == CHOOSE x \in S : \A y \in S : x >= y
MinOf(S) == CHOOSE x \in S : \A y \in S : x <= y

\* generalized reduction (fold) over a set, combine-func is a binary operator
FoldSet(S, zero, combine) ==
    LET g[S2 \in SUBSET S] ==
        IF S2 = {} THEN zero
        ELSE LET x == CHOOSE y \in S2 : TRUE
                 rest == S2 \ {x}
                 folded == g[rest]
             IN combine(x, folded)
    IN g[S]

\* reduction over a sequence; the library's FoldSeq expects a binary operator and the
\* accumulation order it uses is exactly the order needed here
FoldSeq(seq, zero, combine) == CombineSeq(seq, zero, combine)

\* find the index of an element in a sequence; returns 1 if the element is absent
IndexOf(seq, e) ==
    LET g[i \in 1..Len(seq)] ==
        IF i > Len(seq) THEN 1
        ELSE IF seq[i] = e THEN i
        ELSE g[i + 1]
    IN g[1]

\* convert a sequence to a set of its elements
SeqToSet(seq) == {seq[i] : i \in 1..Len(seq)}

\* last element of a nonempty sequence
Last(seq) == seq[Len(seq)]

\* sequence emptiness test
Empty(seq) == Len(seq) = 0

\* remove all occurrences of element e from a sequence
RemoveAll(seq, e) ==
    [i \in 1..(Len(seq) - Cardinality({j \in 1..Len(seq) : seq[j] = e})) |-> LET k == IndexOf(seq, e) IN IF i < k THEN seq[i] ELSE seq[i + 1]]

\* intersection of a set of sets
InterOfSets(S) ==
    IF S = {} THEN {}
    ELSE LET x == CHOOSE y \in S : TRUE IN x \cap InterOfSets(S \ {x})

\* all permutation sequences of a finite set v
Permutations(v) ==
    IF v = {} THEN {<<>>}
    ELSE {<<x>> \o p : x \in v, p \in Permutations(v \ {x})}

\* test helper: validate a condition, printing a diagnostic message on failure
Expect(condition, msg) == IF condition THEN TRUE ELSE (Print(msg); FALSE)

====