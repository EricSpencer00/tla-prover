---- MODULE Util ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
  Elem, MaxVal

RECURSIVE SetIntersection(_, _)
SetIntersection(S, T) ==
  \E x \in S : x \in T

RECURSIVE MaxElem(_, _)
MaxElem(f, S) ==
  IF S = {} THEN f
  ELSE LET x == CHOOSE y \in S : \A z \in S : f[y] >= f[z]
       IN x

RECURSIVE MinElem(_, _)
MinElem(f, S) ==
  IF S = {} THEN f
  ELSE LET x == CHOOSE y \in S : \A z \in S : f[y] <= f[z]
       IN x

RECURSIVE SetFold(_, _, _)
SetFold(f, S, z) ==
  IF S = {} THEN z
  ELSE \E a \in S :
       SetFold(f, S \ {a}, f(z, a))

RECURSIVE SeqFold(_, _, _)
SeqFold(f, s, z) ==
  IF s = << >> THEN z
  ELSE f(z, Head(s), SeqFold(f, Tail(s), z))

RECURSIVE IndexOf(_, _)
IndexOf(s, x) ==
  IF s = << >> THEN -1
  ELSE IF Head(s) = x THEN 1
  ELSE LET i == IndexOf(Tail(s), x)
       IN IF i = -1 THEN -1 ELSE i + 1

RECURSIVE ToSet(_)
ToSet(s) ==
  IF s = << >> THEN {}
  ELSE {Head(s)} \cup ToSet(Tail(s))

LastElem(s) ==
  IF s = << >> THEN CHOOSE x \in Elem : TRUE
  ELSE Head(Reverse(s))

IsEmpty(s) ==
  s = << >>

RECURSIVE RemoveAll(_, _)
RemoveAll(s, x) ==
  IF s = << >> THEN << >>
  ELSE IF Head(s) = x THEN RemoveAll(Tail(s), x)
  ELSE << Head(s) >> \o RemoveAll(Tail(s), x)

RECURSIVE SetOfSetsIntersection(_)
SetOfSetsIntersection(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE
       IN x \cap SetOfSetsIntersection(S \ {x})

RECURSIVE Permutations(_)
Permutations(S) ==
  IF S = {} THEN {<< >>}
  ELSE { << x >> \o p
         : x \in S, p \in Permutations(S \ {x}) }

RECURSIVE TestHelper(_)
TestHelper(f) ==
  LET v == CHOOSE x \in Elem : TRUE
   IN IF f(v) THEN TRUE ELSE ~f(v)

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====