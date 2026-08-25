---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

VARIABLE dummy

(* Dummy state for specification *)
INIT == dummy = 0

NEXT == UNCHANGED dummy

SPECIFICATION == INIT /\ [][NEXT]_<<dummy>>

INVARIANTS == {}

PROPERTIES == {}

(* Utility operators *)

SetOverlap(S1, S2) == ∃ x ∈ S1 : x ∈ S2

SetMax(S) ==
  IF S = {} THEN NULL
  ELSE CHOOSE x ∈ S : ∀ y ∈ S : y <= x

SetMin(S) ==
  IF S = {} THEN NULL
  ELSE CHOOSE x ∈ S : ∀ y ∈ S : x <= y

SetFold(S, Op(_,_), Init) ==
  IF S = {} THEN Init
  ELSE
    LET x == CHOOSE y ∈ S : TRUE
    IN SetFold(S \ {x}, Op, Op(Init, x))

SeqFold(seq, Op(_,_), Init) ==
  IF Len(seq) = 0 THEN Init
  ELSE
    LET rest == SubSeq(seq, 1, Len(seq) - 1)
        lastElem == seq[Len(seq)]
    IN SeqFold(rest, Op, Op(Init, lastElem))

IndexOf(seq, elem) ==
  IF elem ∈ SeqToSet(seq) THEN
    CHOOSE i ∈ 1..Len(seq) : seq[i] = elem
  ELSE 0

SeqToSet(seq) == { seq[i] : i ∈ 1..Len(seq) }

SeqLast(seq) == seq[Len(seq)]

SeqIsEmpty(seq) == Len(seq) = 0

SeqRemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF seq[1] = elem THEN SeqRemoveAll(SubSeq(seq, 2, Len(seq)), elem)
  ELSE << seq[1] >> \o SeqRemoveAll(SubSeq(seq, 2, Len(seq)), elem)

SetIntersectionAll(SS) == INTERSECTION(SS)

Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE
    UNION { << x >> \o p : x ∈ S, p ∈ Permutations(S \ {x}) }

TestHelper(expr, msg) == expr

====