---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS X, Y, Z

\* Utility operators shared across the key-value store specifications:
\*   * SetIntersect: test whether two sets overlap
\*   * MaxOf and MinOf: maximum and minimum element selection from a set
\*   * SetReduce: generalized set reduction (fold over a set)
\*   * SeqReduce: generalized sequence reduction (fold over a sequence)
\*   * SeqIndexOf: find the index of an element in a sequence
\*   * SeqToSet: convert a sequence to the set of its elements
\*   * LastOf: get the last element of a sequence
\*   * EmptySeq: test if a sequence is empty
\*   * RemoveAll: remove all occurrences of an element from a sequence
\*   * IntersectSets: intersect a set of sets
\*   * Permutations: generate all permutation sequences of a finite set
\*   * TestHelper: an assertion wrapper that prints diagnostic information on failure

\* SPECIFICATION, INIT, NEXT, INVARIANTS, and PROPERTIES are defined as
\* no-op placeholders, required because the .cfg mentions them though no
\* actions or invariants are actually specified in this library module.

Spec == TRUE

Init == TRUE

Next == TRUE

TypeOK == TRUE

SpecOK == TRUE

SPECIFICATION Spec

INIT Init

NEXT Next

INVARIANT TypeOK

PROPERTY SpecOK

SetIntersect(A, B) == \E a \in A : a \in B

MaxOf(S) == CHOOSE x \in S : \A y \in S : y <= x

MinOf(S) == CHOOSE x \in S : \A y \in S : x <= y

SetReduce(f, base, S) ==
    LET g[T \in SUBSET S] ==
        IF T = {} THEN base
        ELSE LET x == CHOOSE y \in T : TRUE
             IN f[x, g[T \ {x}]]
    IN g[S]

SeqReduce(f, base, s) ==
    LET g[i \in 0..Len(s)] ==
        IF i = 0 THEN base
        ELSE f[s[i], g[i - 1]]
    IN g[Len(s)]

SeqIndexOf(s, e) == CHOOSE i \in 1..Len(s) : s[i] = e

SeqToSet(s) == {s[k] : k \in 1..Len(s)}

LastOf(s) == s[Len(s)]

EmptySeq(s) == Len(s) = 0

RemoveAll(s, e) == SelectSeq(s, LAMBDA x : x # e)

IntersectSets(T) == FoldSet(\A \in DOMAIN T : T[\A], {}, SetIntersect)

\* Permutations of a set: generate every ordering as a sequence; the
\* recursion builds suffixes from the tail set, then prefixes each with
\* the current head element.
Permutations(S) ==
    IF S = {} THEN {<<>>}
    ELSE {<<e>> \o t : e \in S, t \in Permutations(S \ {e})}

TestHelper(f, x) == f(x) \/ (Print("test failed on", x); FALSE)

====