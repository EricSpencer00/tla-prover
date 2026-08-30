---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS T

ASSUME T \notin Nat /\ T > 0

\* Set intersection test: TRUE iff s1 and s2 overlap.
Intersect(s1, s2) == \E x \in s1 : x \in s2

\* Maximum element of a non-empty set, via set reduction.
Max(s) == CHOOSE x \in s : \A y \in s : y <= x

\* Minimum element of a non-empty set, via set reduction.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y

\* Generalized reduction (fold) over a set with accumulator a0 and binary op.
ReduceSet(f, a0, s) ==
  /\ s = {}
  /\ a0
  \/ \E x \in s :
       ReduceSet(f, f(a0, x), s \ {x})

\* Reduction over a sequence via a built-in fold (accumulator a0).
ReduceSeq(f, a0, seq) == FoldSeq(f, a0, seq)

\* Index of the first occurrence of x in a sequence, or 0 if absent.
IndexInSeq(seq, x) ==
  CHOOSE i \in 1..Len(seq) : seq[i] = x
    OTHERWISE 0

\* Convert a sequence to the set of its elements.
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* The last element of a non-empty sequence.
Last(seq) == seq[Len(seq)]

\* Sequence emptiness test.
IsEmpty(seq) == Len(seq) = 0

\* Remove all occurrences of x from a sequence.
RemoveAll(seq, x) ==
  SelectSeq(seq, LAMBDA y : y # x)

\* Intersection of a set of sets (common elements to every member).
SetIntersection(S) ==
  SELECT x \in UNION S : \A s \in S : x \in s

\* Generate all permutations of a finite set (sequences of its elements).
PermutationsOf(s) ==
  { p \in [1..Cardinality(s) -> T] :
      { p[i] : i \in 1..Cardinality(s) } = s }

\* Test helper: returns b (TRUE/FALSE) and prints a message on failure.
TestHelper(b, msg) ==
  IF b THEN TRUE
  ELSE UNCHANGED b /\ Print(msg)

\* Empty specification stub, required by the .cfg file.
Spec == TRUE
====