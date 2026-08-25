---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* --------------------------------------------------------------
\* Set utilities
\* --------------------------------------------------------------

SetOverlap(A, B) == (A \cap B) # {}

SetMax(S) ==
  IF S = {} THEN NULL
  ELSE CHOOSE x \in S : \A y \in S : y <= x

SetMin(S) ==
  IF S = {} THEN NULL
  ELSE CHOOSE x \in S : \A y \in S : x <= y

\* Generalized reduction (fold) over a set.
RECURSIVE SetReduce(_,_ ,_)
SetReduce(S, init, f) ==
  IF S = {} THEN init
  ELSE
    LET a == ANY x \in S : TRUE \* arbitrary element of S
    IN SetReduce(S \ {a}, f(init, a), f)

\* Intersection of a set of sets.
RECURSIVE SetIntersection(_)
SetIntersection(SS) ==
  IF SS = {} THEN {}
  ELSE
    LET s == ANY x \in SS : TRUE
    IN s \cap SetIntersection(SS \ {s})

\* --------------------------------------------------------------
\* Sequence utilities
\* --------------------------------------------------------------

SeqReduce(seq, init, f) == FoldSeq(seq, init, f)

IndexOf(seq, e) ==
  IF e \in seq THEN
    CHOOSE i \in DOMAIN seq : seq[i] = e
  ELSE -1

SeqToSet(seq) == { seq[i] : i \in DOMAIN seq }

Last(seq) == seq[Len(seq)]

IsEmpty(seq) == Len(seq) = 0

RemoveAll(seq, e) ==
  IF Len(seq) = 0 THEN <<>>
  ELSE IF Head(seq) = e
       THEN RemoveAll(Tail(seq), e)
       ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), e)

\* --------------------------------------------------------------
\* Permutations of a finite set
\* --------------------------------------------------------------

Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE UNION { <<e>> \o p : e \in S, p \in Permutations(S \ {e}) }

\* --------------------------------------------------------------
\* Assertion helper (prints diagnostics on failure)
\* --------------------------------------------------------------

AssertEqual(expected, actual, msg) ==
  IF expected = actual
    THEN TRUE
    ELSE (Print(msg, " expected: ", expected,
                " actual: ", actual); FALSE)

====