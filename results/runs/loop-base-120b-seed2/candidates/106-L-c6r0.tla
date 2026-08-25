---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT NULL

VARIABLE dummy

INIT == dummy = 0

NEXT == UNCHANGED dummy

SPECIFICATION == INIT /\ [][NEXT]_<<dummy>>

INVARIANTS == TRUE

PROPERTIES == TRUE

(* Utility operators *)

SetOverlap(S, T) == (S \cap T) # {}

SetMax(S) == IF S = {} THEN NULL ELSE CHOOSE x \in S: \A y \in S: y <= x

SetMin(S) == IF S = {} THEN NULL ELSE CHOOSE x \in S: \A y \in S: x <= y

RECURSIVE SetFold(_,_,_)
SetFold(S, e, f) ==
  IF S = {} THEN e
  ELSE
    LET x == CHOOSE y \in S: TRUE IN
      SetFold(S \ {x}, f(e, x), f)

SeqFold(seq, e, f) == FoldSeq(seq, e, f)

IndexOf(seq, elem) ==
  IF elem \in SeqToSet(seq) THEN
    CHOOSE i \in DOMAIN seq: seq[i] = elem
  ELSE -1

SeqToSet(seq) == {seq[i] : i \in DOMAIN seq}

Last(seq) == IF Len(seq) = 0 THEN NULL ELSE seq[Len(seq)]

IsEmpty(seq) == Len(seq) = 0

RECURSIVE RemoveAll(_,_)
RemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF seq[1] = elem THEN RemoveAll(Tail(seq), elem)
  ELSE <<seq[1]>> \o RemoveAll(Tail(seq), elem)

SetIntersection(SS) == \bigcap SS

PermutationsOf(S) == Permutations(S)

AssertEqual(actual, expected, msg) ==
  IF actual = expected THEN TRUE
  ELSE (Print(msg, " expected=", expected, " actual=", actual); FALSE)

====