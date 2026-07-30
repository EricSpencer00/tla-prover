---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS MaxN, MaxSetSize

VARIABLES index, seen

vars == <<index, seen>>

Name == "Util"

TypeOK ==
    /\ index \in 0 .. MaxSetSize
    /\ seen \in SUBSET [a : 1 .. MaxSetSize, v : 0 .. MaxN]

Init ==
    /\ index = 0
    /\ seen = {}

\* Utility operator: test whether two sets have a non-empty intersection.
\* The name matches the description exactly; the module has no actors.
Overlap(a, b) == \E x \in a : x \in b

\* Utility operator: generalized set reduction (fold over a set with an
\* accumulator).  The accumulator starts at the extreme (Min/Max) of its
\* domain so that the first fold step always replaces it.
Fold(a, f, x) ==
    /\ \E g \in [1 .. Cardinality(a) -> a] :
         LET vals == [i \in 1 .. Cardinality(a) |-> g[i]]
         IN LET y == FoldSeq(vals, f, x)
            IN y

\* Utility operator: sequence reduction (fold over a sequence with an
\* accumulator).  This one is implemented directly in terms of the
\* library's FoldSeq operator.
FoldSeq(seq, f, x) ==
    IF seq = <<>> THEN x ELSE f(seq[1], FoldSeq(Tail(seq), f, x))

\* Utility operator: find the index of an element in a sequence, or zero
\* if the element is absent.  The index is one-based, matching the
\* CountHops operator in the key-value store spec.
Find(seq, elt) ==
    IF seq = <<>> THEN 0
    ELSE IF seq[1] = elt THEN 1
    ELSE LET r == Find(Tail(seq), elt)
         IN IF r = 0 THEN 0 ELSE r + 1

\* Utility operator: convert a sequence into the set of its elements.
SeqToSet(seq) ==
    IF seq = <<>> THEN {}
    ELSE {seq[1]} \cup SeqToSet(Tail(seq))

\* Utility operator: the last element of a non-empty sequence.
Last(seq) == IF Len(seq) = 1 THEN seq[1] ELSE Last(Tail(seq))

\* Utility operator: test if a sequence is empty.
SeqEmpty(seq) == seq = <<>>

\* Utility operator: remove all occurrences of an element from a sequence.
RemoveAll(seq, elt) ==
    IF seq = <<>> THEN <<>>
    ELSE IF seq[1] = elt THEN RemoveAll(Tail(seq), elt)
    ELSE <<seq[1]>> \o RemoveAll(Tail(seq), elt)

\* Utility operator: intersection of a set of sets.
Common(a) ==
    /\ \E b \in a : TRUE
    /\ \E x \in b \in a : TRUE
    /\ {x \in b \in a : \A y \in a : x \in y}

\* Utility operator: generate all permutations of a finite set.
Permutations(a) ==
    LET f[S \in SUBSET (1 .. MaxSetSize)] == IF S = {} THEN {<<>>}
                                        ELSE {<<x>> \o s : x \in S, s \in f[S \ {x}]}
    IN f[a]

\* Utility operator: test helper for writing assertions that prints
\* diagnostic information on failure.  The \A in the expression is
\* never executed because the ASSERT always fails.
Show(expr) == FALSE /\ (\A x \in {expr} : TRUE)

Spec == TRUE
Next == TRUE
INVARIANT Spec
INVARIANT Init

====