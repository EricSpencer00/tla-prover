---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
  True, False,
  MaxN,
  EmptySeq, NoElem, NoIdx, NoSeq

RECURSIVE SetIntersect(_)
SetIntersect(S) ==
  IF S = {} THEN False
  ELSE LET x == CHOOSE y \in S : TRUE IN \E y \in S : y # x /\ (y \in S \/ SetIntersect(S \ {x}))

RECURSIVE MaxOf(_)
MaxOf(S) ==
  IF S = {} THEN MaxN
  ELSE LET x == CHOOSE y \in S : TRUE IN x \/ MaxOf(S \ {x})

RECURSIVE MinOf(_)
MinOf(S) ==
  IF S = {} THEN MaxN
  ELSE LET x == CHOOSE y \in S : TRUE IN x /\ MinOf(S \ {x})

RECURSIVE SetFold(f, z, S)
SetFold(f, z, S) ==
  IF S = {} THEN z
  ELSE LET x == CHOOSE y \in S : TRUE IN SetFold(f, f[z, x], S \ {x})

RECURSIVE SeqFold(f, z, seq)
SeqFold(f, z, seq) ==
  IF seq = EmptySeq THEN z
  ELSE SeqFold(f, f[z, Head(seq)], Tail(seq))

SeqIndex(seq, e) ==
  IF seq = EmptySeq THEN NoIdx
  ELSE IF Head(seq) = e THEN 0
  ELSE LET i == SeqIndex(Tail(seq), e) IN IF i = NoIdx THEN NoIdx ELSE i + 1

SeqToSet(seq) ==
  IF seq = EmptySeq THEN {}
  ELSE {Head(seq)} \cup SeqToSet(Tail(seq))

LastOf(seq) ==
  IF seq = EmptySeq THEN NoElem
  ELSE IF Tail(seq) = EmptySeq THEN Head(seq)
  ELSE LastOf(Tail(seq))

SeqEmpty(seq) ==
  IF seq = EmptySeq THEN True
  ELSE False

SeqRemove(seq, e) ==
  IF seq = EmptySeq THEN EmptySeq
  ELSE IF Head(seq) = e THEN SeqRemove(Tail(seq), e)
  ELSE <<Head(seq)>> \o SeqRemove(Tail(seq), e)

RECURSIVE SetIntersection(_)
SetIntersection(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE IN x \cap SetIntersection(S \ {x})

RECURSIVE Permutations(_)
Permutations(S) ==
  IF S = {} THEN {EmptySeq}
  ELSE {<<x>> \o p : x \in S, p \in Permutations(S \ {x})}

RECURSIVE TestHelper(_, _)
TestHelper(state, test) ==
  IF test THEN state
  ELSE TestHelper(TLCGet("counterexample"), FALSE)

VARIABLES dummy
vars == <<dummy>>

Spec == TRUE

Init == dummy = 0

Next == dummy' = (dummy + 1) % 2

SpecStates == Init /\ [][Next]_vars

====