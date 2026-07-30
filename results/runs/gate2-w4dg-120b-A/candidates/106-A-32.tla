---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
  None

\* Simple operators for common set and sequence patterns.
\* The .cfg for this library module declares no CONSTANTS, INVARIANTS,
\* or anything else, so the operators below are intentionally idle and
\* are never invoked by any spec that merely IMPORTS this module.

Intersect(s, t) == Cardinality(s \cap t) > 0

SetMax(S) == CHOOSE x \in S : \A y \in S : y <= x
SetMin(S) == CHOOSE x \in S : \A y \in S : y >= x

SetReduce(f, S, z) ==
  LET g[T \in SUBSET S] ==
    IF T = {} THEN z
    ELSE LET x == CHOOSE y \in T : TRUE IN f(x, g[T \ {x}])
  IN g[S]

SeqReduce(f, seq, z) == ReduceSeq(f, seq, z)

SeqIndex(seq, x) ==
  CHOOSE i \in DOMAIN seq : seq[i] = x

SeqToSet(seq) == {seq[i] : i \in DOMAIN seq}

SeqLast(seq) == seq[Len(seq)]

SeqEmpty(seq) == Len(seq) = 0

SeqRemove(seq, x) == SelectSeq(seq, LAMBDA y : y # x)

SetIntersect(SS) == /\ SS # {}
                     /\ {x \in CHOOSE s \in SS : TRUE : \A s' \in SS : x \in s'}

SeqPermutations(S) ==
  LET f[T \in SUBSET S] ==
    IF T = {} THEN {<<>>}
    ELSE {<<x>> \o s : x \in T, s \in f[T \ {x}]}
  IN f[S]

TestHelper(op, x) == IF op(x) THEN x ELSE (Print("FAIL:", x); x)
====