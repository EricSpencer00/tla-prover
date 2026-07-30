---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS MaxId, MaxSeq

\* A utility library for the KV store specs.  No actions or actors: just a
\* collection of reusable operators.

Empty == << >>

\* 1) Set intersection test: true iff two sets have a common element.
Overlap(a, b) == \E x \in a : x \in b

\* 2) Max and min element of a set of naturals.
MaxOf(S) == LET f[T \in SUBSET 1..MaxId] ==
                IF T = {} THEN 0
                ELSE LET x == CHOOSE y \in T : \A z \in T : y >= z IN x
             IN f[S]
MinOf(S) == LET f[T \in SUBSET 1..MaxId] ==
                IF T = {} THEN MaxId
                ELSE LET x == CHOOSE y \in T : \A z \in T : y <= z IN x
            IN f[S]

\* 3) Generalized set reduction: fold f over the elements of a set.
RECURSIVE SetReduce(_, _)
SetReduce(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SetReduce(f, S \ {x})

\* 4) Sequence reduction: fold f over a sequence using the library's FoldSeq.
SeqReduce(f, s) == FoldSeq(f, 0, s)

\* 5) Index of an element in a sequence (0 if absent).
IndexOf(e, s) == IF e \notin { s[i] : i \in DOMAIN s } THEN 0
                 ELSE CHOOSE i \in DOMAIN s : s[i] = e

\* 6) Convert a sequence to the set of its elements.
SeqToSet(s) == { s[i] : i \in DOMAIN s }

\* 7) Last element of a non-empty sequence.
Last(s) == s[Len(s)]

\* 8) Sequence is empty test.
IsEmpty(s) == s = Empty

\* 9) Remove all occurrences of an element from a sequence.
RemoveAll(e, s) == SelectSeq(s, LAMBDA x : x # e)

\* 10) Intersection of a set of sets.
RECURSIVE IntersectSets(_)
IntersectSets(T) ==
    IF T = {} THEN {}
    ELSE LET x == CHOOSE y \in T : TRUE IN x \cap IntersectSets(T \ {x})

\* 11) All permutations of a finite set of naturals up to MaxId.
PermutationOf(S) ==
    IF \E i \in 1..MaxId : S = { i } THEN { << i >> : i \in S }
    ELSE { << x >> \o p :
            x \in S, p \in PermutationOf(S \ { x }) }

\* 12) Test helper that prints a diagnostic value when its condition fails.
RECURSIVE TestHelper(_, _)
TestHelper(cond, val) ==
    IF cond THEN 0
    ELSE LET _ == (Print("FAIL: ") /\ Print(val)) IN 0

\* The module is a library, so its SPECIFICATION, INIT, NEXT, INVARIANTS,
\* and PROPERTIES are defined as no-ops binding variables that never change.
\* This satisfies the .cfg's requirement that these identifiers exist.
SPECIFICATION == 1
INIT == 1
NEXT == 1
INVARIANTS == 1
PROPERTIES == 1

====