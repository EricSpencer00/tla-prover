---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS None

\* Generalized set reduction (fold over a set with an accumulator).
\* Operand: f, a binary operator; init, the initial accumulator; S, the set.
\* Returns the result of folding f over the elements of S, in no fixed order.
RECURSIVE SetReduce(_)
SetReduce(S) == IF S = {} THEN init
                ELSE LET x == CHOOSE e \in S : TRUE
                         rest == SetReduce(S \ {x})
                     IN f(x, rest)

\* Generalized sequence reduction, using the library's FoldSeq operator.
\* Operand: f, a binary operator; init, the initial accumulator; seq, the sequence.
SeqReduce(f, init, seq) == FoldSeq(f, init, seq)

\* Returns TRUE iff two sets intersect (share at least one element), FALSE otherwise.
SetIntersects(S, T) == \E x \in S : x \in T

\* Returns the maximum element of a non-empty set of naturals.
\* Precondition: S is non-empty and bounded above.
SetMax(S) == LET m == CHOOSE y \in S : \A z \in S : z <= y IN m

\* Returns the minimum element of a non-empty set of naturals.
\* Precondition: S is non-empty and bounded below.
SetMin(S) == LET m == CHOOSE y \in S : \A z \in S : y <= z IN m

\* Returns the index of the first occurrence of x in the non-empty sequence seq.
SeqIndex(seq, x) ==
  IF seq = <<>> THEN -1
  ELSE IF Head(seq) = x THEN 1
  ELSE LET rest == SeqIndex(Tail(seq), x)
       IN IF rest = -1 THEN -1 ELSE rest + 1

\* Returns the set of elements appearing in the sequence seq.
SeqToSet(seq) == {seq[k] : k \in DOMAIN seq}

\* Returns the last element of a non-empty sequence seq.
SeqLast(seq) ==
  IF seq = <<>> THEN None
  ELSE IF Tail(seq) = <<>> THEN Head(seq)
  ELSE SeqLast(Tail(seq))

\* Returns TRUE when the sequence seq is empty, FALSE otherwise.
SeqIsEmpty(seq) == seq = <<>>

\* Returns the sequence seq with every occurrence of x removed.
SeqRemove(seq, x) ==
  IF seq = <<>> THEN <<>>
  ELSE IF Head(seq) = x THEN SeqRemove(Tail(seq), x)
  ELSE <<Head(seq)>> \o SeqRemove(Tail(seq), x)

\* Returns the intersection of a non-empty set of sets.
SetIntersection(SS) ==
  CHOOSE y \in SS : TRUE

\* Returns the set of all permutation sequences of the set S.
Permutations(S) ==
  IF S = {} THEN {}
  ELSE {s \o rest : s \in S : rest \in Permutations(S \ {s})}

\* Test helper: asserts a boolean condition and prints diagnostics on failure.
\* Intended for use in assertions inside specifications or model actions.
TestHelper(cond, msg) ==
  IF cond THEN TRUE ELSE PrintString(msg) = msg

====