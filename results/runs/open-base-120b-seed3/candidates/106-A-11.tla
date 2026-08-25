---- MODULE Util ----
EXTENDS Naturals, Sequences, TLC

\* ---------- Utility Operators ----------
Overlap(s, t) == s \cap t # {}

MaxSet(S) == IF S = {} THEN NULL ELSE CHOOSE x \in S: \A y \in S: y <= x

MinSet(S) == IF S = {} THEN NULL ELSE CHOOSE x \in S: \A y \in S: x <= y

SetFold(F, A, S) ==
  IF S = {} THEN A
  ELSE
    LET e == CHOOSE x \in S
    IN SetFold(F, F(A, e), S \ {e})

Tail(s) ==
  IF Len(s) <= 1 THEN <<>>
  ELSE [i \in 1..(Len(s) - 1) |-> s[i + 1]]

SeqFold(F, A, s) ==
  IF Len(s) = 0 THEN A
  ELSE SeqFold(F, F(A, s[1]), Tail(s))

IndexOf(seq, elem) ==
  IF \E i \in 1..Len(seq) : seq[i] = elem
  THEN CHOOSE i \in 1..Len(seq) : seq[i] = elem
  ELSE 0

SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

Last(seq) == IF Len(seq) = 0 THEN NULL ELSE seq[Len(seq)]

IsEmpty(seq) == Len(seq) = 0

RemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF seq[1] = elem
       THEN RemoveAll(Tail(seq), elem)
       ELSE <<seq[1]>> \o RemoveAll(Tail(seq), elem)

SetIntersection(SS) == { x \in UNION SS : \A Y \in SS : x \in Y }

Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

TestAssert(cond, msg) ==
  IF cond THEN TRUE ELSE (Print(msg); FALSE)

\* ---------- Required Specification Skeleton ----------
VARIABLE dummy

INIT == dummy = 0

NEXT == UNCHANGED dummy

SPECIFICATION == INIT /\ [][NEXT]_<<dummy>>

INVARIANTS == {}

PROPERTIES == {}

====