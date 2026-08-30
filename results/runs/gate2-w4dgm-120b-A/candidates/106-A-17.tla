---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS EmptySeq, EmptySet

\* Intersection test: true iff two sets share at least one element.
Intersect(p, q) == \E x \in p : x \in q

\* Maximum and minimum of a non-empty finite set of naturals.
SetMax(S) == CHOOSE m \in S : \A x \in S : x <= m
SetMin(S) == CHOOSE m \in S : \A x \in S : m <= x

\* Generalized reduction (fold) over the elements of a set.
SetReduce(f, S, base) == LET
    g[T \in SUBSET S] ==
        IF T = {} THEN base
        ELSE LET x \in T : f[x, g[T \ {x}]]
  IN g[S]

\* Sequence reduction: fold over a sequence with an accumulator.
SeqReduce(f, seq, base) == LET
    g[i \in 0..Len(seq)] ==
        IF i = 0 THEN base
        ELSE f[seq[i], g[i - 1]]
  IN g[Len(seq)]

\* Find the index of an element in a sequence (0 if absent).
SeqIndex(seq, x) == CHOOSE i \in 1..Len(seq) : seq[i] = x
SeqFind(seq, x) == IF \E i \in 1..Len(seq) : seq[i] = x
                   THEN SeqIndex(seq, x) ELSE 0

\* Convert a sequence to the set of its elements.
SeqToSet(seq) == {seq[i] : i \in 1..Len(seq)}

\* Last element of a non-empty sequence; arbitrary constant on EmptySeq.
SeqLast(seq) == IF seq = EmptySeq THEN EmptySet ELSE seq[Len(seq)]

\* Empty-sequence test.
SeqEmpty(seq) == seq = EmptySeq

\* Remove all occurrences of a value from a sequence.
SeqRemove(seq, x) == SelectSeq(seq, LAMBDA y : y # x)

\* Intersection of a set of sets; EmptySet for the empty family.
FamilyIntersect(F) == IF F = {} THEN EmptySet
                     ELSE SetReduce(Intersect, F, CHOOSE x \in F : x)

\* Generate all permutations of a finite set as sequences.
Permutations(S) == { p \in Seq(S) : Cardinality(SeqToSet(p)) = Cardinality(S) }

\* Assertion test with a diagnostic tag for easier debugging.
TaggedAssert(b, msg) == IF b THEN TRUE
                        ELSE /\ msg \in {"Error"} /\ UNCHANGED msg

\* No-op default definitions to satisfy the .cfg expectations when no
\* actions are otherwise specified.
SPECIFICATION == TRUE
INIT == TRUE
NEXT == UNCHANGED <<>>
INVARIANTS == {}
PROPERTIES == {}
====