---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

\* ---------- Set utilities ----------
Overlap(S, T) == \E x \in S : x \in T

SetMax(S) == 
  IF S = {} THEN NULL 
  ELSE CHOOSE x \in S : \A y \in S : y <= x

SetMin(S) == 
  IF S = {} THEN NULL 
  ELSE CHOOSE x \in S : \A y \in S : x <= y

SetReduce(S, init, f) ==
  IF S = {} THEN init
  ELSE LET a == CHOOSE x \in S IN
       SetReduce(S \ {a}, f(init, a), f)

SetIntersection(SS) ==
  IF SS = {} THEN {}
  ELSE LET S0 == CHOOSE S \in SS IN
       { x \in S0 : \A T \in SS : x \in T }

\* ---------- Sequence utilities ----------
SeqReduce(seq, init, f) ==
  IF Len(seq) = 0 THEN init
  ELSE f(SeqReduce(SubSeq(seq, 1, Len(seq) - 1), init, f), seq[Len(seq)])

SeqIndex(seq, elem) ==
  IF \E i \in 1..Len(seq) : seq[i] = elem
  THEN CHOOSE i \in 1..Len(seq) : seq[i] = elem
  ELSE 0

SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

SeqLast(seq) ==
  IF Len(seq) = 0 THEN NULL ELSE seq[Len(seq)]

SeqIsEmpty(seq) == Len(seq) = 0

SeqRemoveAll(seq, elem) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF seq[1] = elem
       THEN SeqRemoveAll(SubSeq(seq, 2, Len(seq)), elem)
       ELSE << seq[1] >> \o SeqRemoveAll(SubSeq(seq, 2, Len(seq)), elem)

\* ---------- Permutations ----------
Permutations(S) ==
  IF S = {} THEN { << >> }
  ELSE UNION { << e >> \o p : e \in S, p \in Permutations(S \ {e}) }

\* ---------- Assertion helper ----------
AssertHelper(cond, msg) ==
  IF cond THEN TRUE ELSE Print(msg) /\ FALSE

====