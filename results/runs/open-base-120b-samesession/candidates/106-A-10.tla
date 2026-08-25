---- MODULE Util ----
EXTENDS Naturals, Sequences

(* Utility operators *)

SetOverlap(A, B) == \E x \in A : x \in B

MaxElement(S) ==
  IF S = {} THEN NULL
  ELSE CHOOSE x \in S : \A y \in S : y <= x

MinElement(S) ==
  IF S = {} THEN NULL
  ELSE CHOOSE x \in S : \A y \in S : x <= y

SetReduce(S, op, init) ==
  IF S = {} THEN init
  ELSE LET e == CHOOSE x \in S IN SetReduce(S \ {e}, op, op(init, e))

SeqTail(s) ==
  IF Len(s) = 0 THEN <<>>
  ELSE [i \in 1..(Len(s) - 1) |-> s[i + 1]]

SeqReduce(s, op, init) ==
  IF Len(s) = 0 THEN init
  ELSE SeqReduce(SeqTail(s), op, op(init, s[1]))

IndexOf(s, elem) ==
  IF \E i \in 1..Len(s) : s[i] = elem
  THEN Min({ i \in 1..Len(s) : s[i] = elem })
  ELSE NULL

SeqToSet(s) == { s[i] : i \in 1..Len(s) }

Last(s) ==
  IF Len(s) = 0 THEN NULL ELSE s[Len(s)]

IsEmpty(s) == Len(s) = 0

RemoveAll(s, elem) ==
  IF Len(s) = 0 THEN <<>>
  ELSE IF s[1] = elem
       THEN RemoveAll(SeqTail(s), elem)
       ELSE << s[1] >> \o RemoveAll(SeqTail(s), elem)

IntersectSetOfSets(T) ==
  IF T = {} THEN {}
  ELSE { x \in CHOOSE S \in T : S : \A Y \in T : x \in Y }

Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

Print(msg) == TRUE

TestHelper(cond, msg) ==
  IF cond THEN TRUE ELSE (Print(msg) /\ FALSE)

(* Trivial specification placeholders *)

INIT == TRUE

NEXT == UNCHANGED <<>>

SPECIFICATION == INIT /\ [][NEXT]_<<>>

INVARIANTS == {}

PROPERTIES == {}

====