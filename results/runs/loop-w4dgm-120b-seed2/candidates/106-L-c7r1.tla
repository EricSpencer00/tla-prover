---- MODULE Util ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS MaxVal, MaxN

VARIABLES lastReduced, lastSetReduce, lastPerm

vars == <<lastReduced, lastSetReduce, lastPerm>>

Intersects(A, B) == \E x \in A : x \in B

MaxOf(S) == CHOOSE m \in S : \A x \in S : x <= m
MinOf(S) == CHOOSE m \in S : \A x \in S : m <= x

SetFold(f, S, a) ==
  IF S = {} THEN a
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x, SetFold(f, S \ {x}, a)]

SeqFold(f, s, a) == FoldSeq(f, a, s)

IndexOf(s, x) ==
  CHOOSE i \in DOMAIN s : s[i] = x

SeqToSet(s) == {s[i] : i \in DOMAIN s}

Last(s) == s[Len(s)]

SeqEmpty(s) == IF s = <<>> THEN TRUE ELSE FALSE

SeqRemoveAll(s, x) ==
  IF s = <<>> THEN <<>>
  ELSE IF Head(s) = x THEN SeqRemoveAll(Tail(s), x)
  ELSE <<Head(s)>> \o SeqRemoveAll(Tail(s), x)

SetIntersectionOf(P) ==
  IF P = {} THEN {}
  ELSE LET x == CHOOSE y \in P : TRUE IN x \cap SetIntersectionOf(P \ {x})

PermutationsOf(S) ==
  {p \in SeqToSet(Permutations(S)) : Cardinality(SeqToSet(p)) = Cardinality(S)}

Init ==
  /\ lastReduced = "none"
  /\ lastSetReduce = 0
  /\ lastPerm = {}

PermStep ==
  /\ lastPerm = {}
  /\ \E s \in PermutationsOf(1..MaxN) : lastPerm' = s
  /\ UNCHANGED <<lastReduced, lastSetReduce>>

Next == PermStep

Spec == Init /\ [][Next]_vars

NoOp == TRUE

TypeOK == NoOp

====