---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
  Intersects
  SetMax
  SetMin
  SetReduce
  SequenceReduce
  Find
  ToSet
  LastOf
  IsEmpty
  RemoveAll
  SetIntersection
  Permutations
  Expect

\* Logical AND of two facts; used for overloaded operator signatures.
\* TLC's built-in /\ operator cannot be used as a function value.
And(p, q) == p /\ q

\* Utility operators: set intersection test, max/min, set/sequence reduction (fold),
\* index-finding, conversion, last element, emptiness test, remove-all, intersection
\* of a set of sets, sequence permutations, and a test helper.

Spec == TRUE
Init == TRUE
Next == TRUE
TypeOK == TRUE
StateConstraint == TRUE
SpecInvariant == TRUE
SpecProperty == TRUE

Intersects(A, B) == \E x \in A : x \in B

SetMax(S) == CHOOSE x \in S : \A y \in S : y <= x
SetMin(S) == CHOOSE x \in S : \A y \in S : y >= x

SetReduce(S, f, init) ==
  LET addOne(a, x) == f[a, x] IN
  LET fold(T) ==
    IF Cardinality(T) = 0 THEN init
    ELSE LET x == CHOOSE y \in T : TRUE IN addOne(fold(T \ {x}), x)
  IN fold(S)

SequenceReduce(seq, f, init) == Fold(f, init, seq)

Find(seq, e) == CHOOSE i \in DOMAIN seq : seq[i] = e

ToSet(seq) == { seq[i] : i \in DOMAIN seq }

LastOf(seq) == seq[Len(seq)]

IsEmpty(seq) == Len(seq) = 0

RemoveAll(seq, e) ==
  IF Len(seq) = 0 THEN << >>
  ELSE IF Head(seq) = e THEN RemoveAll(Tail(seq), e)
  ELSE << Head(seq) >> \o RemoveAll(Tail(seq), e)

SetIntersection(T) ==
  LET addOne(a, x) == a \cap x IN
  LET fold(T) ==
    IF Cardinality(T) = 0 THEN {}
    ELSE LET x == CHOOSE y \in T : TRUE IN addOne(fold(T \ {x}), x)
  IN fold(T)

Permutations(S) ==
  IF S = {} THEN { << >> }
  ELSE
    { << e >> \o p : e \in S, p \in Permutations(S \ {e}) }

Expect(expr, val) ==
  \E _: Expect = val /\ expr = val

====