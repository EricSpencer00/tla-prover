---- MODULE Util ----
EXTENDS Naturals, Sequences

CONSTANTS

SPECIFICATION == "Spec"

Init == TRUE

Next == TRUE

INVARIANTS == {}

PROPERTIES == {}

Intersects(s, t) == \E x \in s : x \in t

SetMaximum(S) == CHOOSE m \in S : \A x \in S : x <= m

SetMinimum(S) == CHOOSE m \in S : \A x \in S : m <= x

SetFold(S, f, a) ==
  LET g[T \in SUBSET S] ==
       IF T = {} THEN a
       ELSE LET x == CHOOSE y \in T : TRUE
            IN f[g[T \ {x}], x]
  IN g[S]

SeqFold(seq, f, a) ==
  IF seq = <<>> THEN a
  ELSE f[SeqFold(Tail(seq), f, a), Head(seq)]

SeqIndexOf(seq, x) ==
  LET g[i \in 0 .. Len(seq)] ==
       IF i = Len(seq) THEN -1
       ELSE IF seq[i + 1] = x THEN i + 1 ELSE g[i + 1]
  IN g[0]

SeqToSet(seq) ==
  { seq[i] : i \in 1 .. Len(seq) }

SeqLast(seq) == seq[Len(seq)]

SeqEmpty(seq) == Len(seq) = 0

SeqRemoveAll(seq, x) ==
  IF seq = <<>> THEN seq
  ELSE IF Head(seq) = x THEN SeqRemoveAll(Tail(seq), x)
  ELSE <<Head(seq)>> \o SeqRemoveAll(Tail(seq), x)

SetIntersectionOf(S) ==
  { x \in UNION S : \A t \in S : x \in t }

SetPermutations(S) ==
  { p \in [1 .. Cardinality(S) -> S] :
       {p[i] : i \in 1 .. Cardinality(S)} = S }

AssertEq(a, b) == a = b

====