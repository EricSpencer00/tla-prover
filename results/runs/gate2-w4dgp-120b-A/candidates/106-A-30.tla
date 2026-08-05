---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences

\* A utility library shared across the key-value store specifications.  It
\* supplies a family of helper operators for set and sequence
\* manipulation: intersection testing, set min/max, folding over sets and
\* sequences, sequence indexing, permutation generation, and a debugging
\* assertion helper.

CONSTANTS
    Elem

VARIABLES
    sigma  \* A sequence of Elem values (used by the permutation generator
             \* and exercised by the test harness)

VARIABLES == {sigma}

\* Set intersection: the two sets share at least one element.
Intersect(s, t) == s \cap t # {}

\* Maximum and minimum element of a non-empty set.
SetMax(S) == CHOOSE m \in S : \A x \in S : x <= m
SetMin(S) == CHOOSE m \in S : \A x \in S : m <= x

\* Generalized reduction (fold) over a set with an accumulator.
SetReduce(S, init, g) ==
    LET f[T \in SUBSET S] ==
        IF T = {} THEN init
        ELSE LET x == CHOOSE y \in T : TRUE
                 rest == f[T \ {x}]
             IN g(x, rest)
    IN f[S]

\* Reduction over a sequence: delegates to the library's foldl operator.
SeqReduce(seq, init, g) == Foldl(seq, init, g)

\* Find the first index of an element in a sequence, or 0 if absent.
SeqIndex(seq, x) ==
    CHOOSE i \in {1..Len(seq)} : seq[i] = x

\* The set of elements present in a sequence.
SeqToSet(seq) == {seq[i] : i \in {1..Len(seq)}}

\* The last element of a non-empty sequence.
SeqLast(seq) == seq[Len(seq)]

\* Sequence empty test for readability.
SeqEmpty(seq) == Len(seq) = 0

\* Remove all occurrences of an element from a sequence.
SeqRemove(seq, x) ==
    [i \in 1..(Len(seq) - Cardinality({j \in {1..Len(seq)} : seq[j] = x}))
        |-> CHOOSE k \in {j \in {1..Len(seq)} : seq[j] # x} :
              k = CHOOSE c \in {j \in {1..Len(seq)} : seq[j] # x} : c > 0 : c]

\* Intersection of a set of sets: elements common to every member set.
SetIntersectionFamily(F) ==
    {x \in UNION F : \A t \in F : x \in t}

\* All permutation sequences of a finite set.
Permutations(S) ==
    LET f[T \in SUBSET S] ==
        IF T = {} THEN << >>
        ELSE LET x == CHOOSE y \in T : TRUE
                 rest == f[T \ {x}]
                 app(e, s) == << e >> \o s
             IN UNION {app(x, s) : s \in rest}
    IN f[S]

\* Test helper: TRUE if the condition holds; FALSE with a printed message otherwise.
AssertHelper(cond, msg) == IF cond THEN TRUE ELSE
    (Print(msg); FALSE)

Init ==
    /\ sigma = << >>

Next ==
    \/ \E x \in Elem :
        /\ sigma' = sigma \o << x >>
        /\ UNCHANGED sigma
    \/ sigma # << >> /\ sigma' = << >> /\ UNCHANGED sigma

Spec == Init /\ [][Next]_sigma

\* Debugging helper: every execution explores at least one transition.
SpecExploresTransitions == Spec

====