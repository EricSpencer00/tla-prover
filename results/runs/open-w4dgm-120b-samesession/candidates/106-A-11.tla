---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Elements, MaxSeqLen

INSeq(x, s) == \E i \in DOMAIN s : s[i] = x
SumSeq(s) == LET g[T \in SUBSET Elements] ==
                 IF T = {} THEN 0
                 ELSE LET x == CHOOSE y \in T : TRUE
                      IN x + g[T \ {x}]
             IN g[Elements]

\* Reduce a finite set with an accumulator, applying f to an arbitrary element
\* drawn from the set and the recursive result on the rest of the set.
FoldSet(f, S, a) == IF S = {} THEN a
                    ELSE \E x \in S : f[x, FoldSet(f, S \ {x}, a)]

\* Reduce a sequence (ordered collection) with an accumulator.
FoldSeq(f, s, a) == IF s = <<>> THEN a
                    ELSE f[Head(s), FoldSeq(f, Tail(s), a)]

Permutations(T) == {p \in Seq(T) : Cardinality(T) = Len(p)}

\* Generate the set of all permutations of the finite set `Elements`.
AllPermutations == Permutations(Elements)
====