---- MODULE Util ----
EXTENDS Integers, Sequences

CONSTANTS MaxSeqLen, MaxSetCard

RECURSIVE IndexOf(_, _)
IndexOf(f, x) ==
  IF f = << >> THEN -1
  ELSE IF Head(f) = x THEN 1
  ELSE LET r == IndexOf(Tail(f), x) IN IF r = -1 THEN -1 ELSE 1 + r

RECURSIVE SetOfSeq(_)
SetOfSeq(f) ==
  IF f = << >> THEN {}
  ELSE {Head(f)} \cup SetOfSeq(Tail(f))

RECURSIVE LastOf(_)
LastOf(f) ==
  IF f = << >> THEN "none"
  ELSE IF Tail(f) = << >> THEN Head(f)
  ELSE LastOf(Tail(f))

RECURSIVE Permutations(_)
Permutations(S) ==
  IF S = {} THEN {<< >>}
  ELSE
    UNION { <<x>> \o p
        : x \in S, p \in Permutations(S \ {x}) }

OneOfRange(f) == IF f = << >> THEN "none" ELSE Head(f)

SpecMaxOp(f) ==
  IF f = << >> THEN "none"
  ELSE LET max2(a, b) == IF a > b THEN a ELSE b IN FoldLeft(max2, f)

SpecMinOp(f) ==
  IF f = << >> THEN "none"
  ELSE LET min2(a, b) == IF a < b THEN a ELSE b IN FoldLeft(min2, f)

RECURSIVE IntersectionOfSets(_)
IntersectionOfSets(S) ==
  IF S = {} THEN {}
  ELSE IF Cardinality(S) = 1 THEN CHOOSE a \in S : TRUE
  ELSE LET a == CHOOSE b \in S : TRUE IN a \cap IntersectionOfSets(S \ {a})

RECURSIVE SetReduce(_, _)
SetReduce(f, S) ==
  IF S = {} THEN f
  ELSE LET x == CHOOSE y \in S : TRUE IN SetReduce(f(x), S \ {x})

RECURSIVE SeqReduce(_, _)
SeqReduce(f, s) ==
  IF s = << >> THEN f
  ELSE SeqReduce(f(Head(s)), Tail(s))

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}
====