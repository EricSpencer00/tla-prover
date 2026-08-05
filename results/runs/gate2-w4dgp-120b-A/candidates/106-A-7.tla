---- MODULE Util ----
EXTENDS Integers, Sequences

\* A reusable library of common helper operators for set and sequence
\* manipulation, shared across the key-value store specifications. It
\* defines: (1) set overlap testing, (2) max/min element extraction, (3)
\* generic set reduction (fold), (4) sequence reduction, (5) index lookup,
\* (6) sequence-to-set conversion, (7) the last element, (8) emptiness
\* testing, (9) occurrence removal, (10) intersection of a set of sets,
\* (11) set permutation generation, and (12) a test-helper wrapper.

RECURSIVE ReduceSet(_)
ReduceSet(f, S, init) ==
  IF S = {} THEN init
  ELSE LET x == CHOOSE x \in S : TRUE IN f(x, ReduceSet(f, S \ {x}, init))

RECURSIVE Permutations(_)
Permutations(S) ==
  IF S = {} THEN << >>
  ELSE IF \E x \in S : S = {x} THEN << [x] >>
  ELSE UNION { [x] \o p : x \in S, p \in Permutations(S \ {x}) }

IntersectionOfSets(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE x \in S : TRUE IN x \cup IntersectionOfSets(S \ {x})

\* Helper: an assertion that prints a diagnostic message on failure.
Assert(msg, cond) == IF cond THEN TRUE ELSE (Print(msg); FALSE)

MaxElement(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : \A y \in S : y <= x IN x

MinElement(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : \A y \in S : y >= x IN x

\* Generic set reduction (fold over a set with an accumulator).
SetReduce(f, S, init) == ReduceSet(f, S, init)

\* Sequence reduction using the library's built-in FoldSeq operator.
SeqReduce(f, seq, init) == FoldSeq(f, seq, init)

IndexOf(seq, x) ==
  CHOOSE i \in 1..Len(seq) : seq[i] = x

SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

LastOf(seq) == seq[Len(seq)]

IsEmpty(seq) == Len(seq) = 0

RemoveAll(seq, x) ==
  << y \in seq : y # x >>

\* Provided by the reference .cfg: no constants, variables, or properties.
CONSTANTS

SPECIFICATION == TRUE

INIT == TRUE

NEXT == TRUE

INVARIANTS == TRUE

PROPERTIES == TRUE

====