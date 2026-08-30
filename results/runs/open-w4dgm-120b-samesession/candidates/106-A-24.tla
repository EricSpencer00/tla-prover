---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NoElem

MyMax(S) == CHOOSE x \in S : \A y \in S : y <= x
MyMin(S) == CHOOSE x \in S : \A y \in S : x <= y

SetFold(f, S, a) == LET g[T \in SUBSET S] ==
  IF T = {} THEN a
  ELSE LET x == CHOOSE y \in T : TRUE
       IN f(x, g[T \ {x}])
  IN g[S]

SeqFold(f, seq) == LET g[k \in 0..Len(seq)] ==
  IF k = 0 THEN NoElem
  ELSE LET x == seq[k]
       IN IF k = 1 THEN x ELSE f(x, g[k - 1])
  IN g[Len(seq)]

SeqIndexOf(seq, x) == CHOOSE k \in 1..Len(seq) : seq[k] = x

SeqSet(seq) == { seq[i] : i \in 1..Len(seq) }

Last(seq) == seq[Len(seq)]

SeqEmpty(seq) == Len(seq) = 0

SeqWithoutAll(seq, x) ==
  IF seq = << >> THEN << >>
  ELSE IF Head(seq) = x THEN SeqWithoutAll(Tail(seq), x)
  ELSE << Head(seq) >> \o SeqWithoutAll(Tail(seq), x)

SetIntersect(P) ==
  { e \in Union(P) : \A Q \in P : e \in Q }

PermutationsOf(S) ==
  { seq \in [1..Cardinality(S) -> S] :
      \A i, j \in 1..Cardinality(S) : (i # j) => seq[i] # seq[j] }

TestHelper(e, pred) ==
  /\ pred
  /\ (e # NoElem) => e = e

====