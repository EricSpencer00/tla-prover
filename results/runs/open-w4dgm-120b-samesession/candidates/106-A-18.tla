---- MODULE Util ----
EXTENDS Naturals, Sequences
CONSTANTS Sets, Elements, Empty, MaxIter

VARIABLES iterCount

Init == iterCount = 0

HasIntersection(s1, s2) == \E x \in s1 : x \in s2

MaxOfSet(s) == CHOOSE m \in s : \A x \in s : x <= m
MinOfSet(s) == CHOOSE m \in s : \A x \in s : m <= x

FoldSet(f, base, s) == LET g[T \in SUBSET s] ==
    IF T = {} THEN base
    ELSE LET x == CHOOSE y \in T : TRUE IN f(g[T \ {x}], x)
  IN g[s]

FoldSeq(f, base, seq) == FoldSeq(f, base, seq, 1)
FoldSeq(f, base, seq, i) ==
  IF i > Len(seq) THEN base
  ELSE f(FoldSeq(f, base, seq, i + 1), seq[i])

IndexOf(seq, x) ==
  CHOOSE i \in 1..Len(seq) : seq[i] = x

SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

LastOfSeq(seq) == seq[Len(seq)]

IsEmpty(seq) == Len(seq) = 0

RemoveAll(seq, x) == SelectSeq(seq, LAMBDA y : y # x)

IntersectAll(sets) == LET g[R \in SUBSET sets] ==
  IF R = {} THEN Elements
  ELSE LET S == CHOOSE y \in R : TRUE IN g[R \ {S}] \cap S
  IN g[sets]

Permutations(set) ==
  IF set = {} THEN {<<>>}
  ELSE { <<x>> \o p : x \in set, p \in Permutations(set \ {x}) }

TestHelper ==
  LET v == 0
  IN \E p \in Permutations(Elements) : v = 0

Next == TRUE

vars == <<iterCount>>

Spec == Init /\ [][Next]_vars
====