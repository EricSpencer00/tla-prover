---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS MaxVal

\* Returns TRUE iff the two sets have any element in common.
SetIntersect(a, b) == \E x \in a : x \in b

\* Returns the maximum element of a non-empty set.
SetMax(s) == CHOOSE x \in s : \A y \in s : y <= x
SetMin(s) == CHOOSE x \in s : \A y \in s : y >= x

\* Generalized reduction (fold) over a set with an accumulator.
SetReduce(f, S, base) == LET rec[T \in SUBSET S] ==
    IF T = {} THEN base
    ELSE LET x == CHOOSE y \in T : TRUE IN f[x, rec[T \ {x}]]
  IN rec[S]

\* Generalized reduction (fold) over a sequence with an accumulator.
SeqReduce(f, seq, base) == FoldSeq(f, seq, base)

SeqIndex(seq, x) == CHOOSE i \in DOMAIN seq : seq[i] = x

SeqToSet(seq) == { seq[i] : i \in DOMAIN seq }

SeqLast(seq) == seq[Len(seq)]

SeqEmpty(seq) == Len(seq) = 0

SeqRemoveAll(seq, x) == SelectSeq(seq, LAMBDA e : e # x)

SetOfSetsIntersect(fam) == CHOOSE x \in UNION fam : \A S \in fam : x \in S

\* Generate all permutations of a finite set via an interleaving insert.
SetPermutations(set) ==
  LET
    InsertAt(x, seq) == [i \in 1..Len(seq) + 1 |-> IF i <= Len(seq) THEN seq[i] ELSE x]
    PermsOf(T) == IF T = {} THEN { <<>> }
                  ELSE UNION { { InsertAt(y, p) : p \in PermsOf(T \ {y}) } : y \in T }
  IN PermsOf(set)

\* Test helper that prints its argument on failure.
TestHelper(x) == CHOOSE b \in BOOLEAN : b

====