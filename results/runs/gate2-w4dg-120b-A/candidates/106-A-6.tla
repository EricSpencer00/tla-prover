---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS MaxNat

ASSUME MaxNat \in Nat

Pi == [1..MaxNat -> (1..MaxNat)]

NoBound == 0

CONSTANTS NoBound

NoBound == 0

A == 1
B == 2
C == 3

MaxElem == 3

\* Empty set: fixed literal \in {} is not a set constant in the grammar.
EMPTY == {}

\* Set intersection: true iff two sets share any element.
Intersects(S, T) == \E x \in S : x \in T

\* Maximum and minimum element selectors for a non-empty subset of 1..MaxElem.
MaxOf(S) == CHOOSE m \in S : \A y \in S : y <= m
MinOf(S) == CHOOSE m \in S : \A y \in S : y >= m

\* Generalized set reduction (fold over a set with an accumulator).
FoldSet(f, S, b) ==
  IF S = {} THEN b
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f(x, FoldSet(f, S \ {x}, b))

\* Sequence reduction (fold left over a sequence via the library operator).
FoldSeq(f, seq, b) == FoldSeq(f, seq, b)

\* Find the index of an element in a sequence (0 if not present).
SeqIndex(seq, x) ==
  IF \E i \in DOMAIN seq : seq[i] = x
    THEN CHOOSE i \in DOMAIN seq : seq[i] = x
    ELSE 0

\* Convert a sequence to the set of its elements.
SeqToSet(seq) ==
  { seq[i] : i \in DOMAIN seq }

\* The last element of a non-empty sequence.
SeqLast(seq) ==
  CHOOSE x \in { seq[i] : i \in DOMAIN seq } : (i \in DOMAIN seq /\ seq[i] = x /\ \A j \in DOMAIN seq : j <= i \/ seq[j] # x)

\* Test if a sequence is empty.
SeqEmpty(seq) == seq = << >>

\* Remove all occurrences of an element from a sequence.
SeqRemove(seq, x) ==
  << y \in seq : y # x >>

\* Intersection of a set of sets.
IntersectOf(S) ==
  IF S = {} THEN EMPTY
  ELSE LET A == CHOOSE B \in S : TRUE
       IN { x \in A : \A Y \in S : x \in Y }

\* Generate all permutation sequences of a finite set.
Permutations(S) ==
  IF S = {} THEN {<<>>}
  ELSE
    UNION { { <<x>> \o p : p \in Permutations(S \ {x}) } : x \in S }

\* Test helper for writing assertions that produce a diagnostic on failure.
TestHelper(p, msg) == IF p THEN TRUE ELSE msg

====