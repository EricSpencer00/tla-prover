---- MODULE Util ----
EXTENDS Integers, Sequences

CONSTANTS

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

SetIntersect(A, B) == \E x \in A : x \in B

SetMax(S) == CHOOSE m \in S : \A x \in S : x <= m
SetMin(S) == CHOOSE m \in S : \A x \in S : m <= x

SetReduce(f, S, init) == LET g[T \in SUBSET S] ==
  IF T = {} THEN init
  ELSE LET x == CHOOSE y \in T : TRUE IN f[g[T \ {x}], x]
  IN g[S]

SeqReduce(f, seq, init) == FoldSeq(f, seq, init)

SeqIndexOf(seq, x) == CHOOSE k \in 1..Len(seq) : seq[k] = x

SeqToSet(seq) == { seq[k] : k \in 1..Len(seq) }

SeqLast(seq) == seq[Len(seq)]

SeqEmpty(seq) == Len(seq) = 0

SeqRemoveAll(seq, x) == SelectSeq(seq, LAMBDA y : y # x)

SetIntersectionOf(S) == { x \in UNION S : \A t \in S : x \in t }

PermutationsOf(S) ==
  IF S = {} THEN { << >> }
  ELSE { << x >> \o p : x \in S, p \in PermutationsOf(S \ {x}) }

TestHelper(expr) == IF expr THEN "Test passed" ELSE "Test failed"
====