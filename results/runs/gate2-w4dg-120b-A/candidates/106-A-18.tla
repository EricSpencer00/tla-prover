---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS PERMUTATIONS_MAXSIZE, MAXVALUE

\* A utility library module providing the common helper operators used by the key-value
\* store specifications. This module has no actors or system components; it is a purely
\* functional library of reusable operators.
\* The operators are: set intersection test, max/min of a set, generalized set reduction,
\* sequence reduction via a fold, element index in a sequence, sequence-to-set conversion,
\* sequence last element, sequence emptiness test, removal of all occurrences of an element
\* from a sequence, set-of-sets intersection, generation of all permutation sequences of a
\* finite set, and a test helper that prints diagnostic information on failure.

\* Set intersection test: whether two sets have any element in common.
SetOverlap(X, Y) == \E x \in X : x \in Y

\* Maximum and minimum element selection from a finite set.
SetMax(S) == CHOOSE m \in S :
                  \A x \in S : x <= m
SetMin(S) == CHOOSE m \in S :
                  \A x \in S : m <= x

\* Generalized set reduction: fold an operator over the elements of a set with an
\* accumulator, the order of folding being nondeterministic (since sets are unordered).
SetFold(f, base, S) ==
  LET combine(a, b) == IF a = base THEN b ELSE f(a, b)
      foldSeq(seq) == IF Len(seq) = 0 THEN base
                       ELSE combine(seq[1], foldSeq(Tail(seq)))
      seqs == { perm \in Permutations(MaxValue) : \E i \in 1..Len(perm) :
                 perm[i] \in S }
  IN \E seq \in seqs : foldSeq(seq)

\* Sequence reduction: fold a binary operator over a sequence with a base value.
SeqFold(f, base, seq) == \E g \in [1..Len(seq) -> 1..Len(seq)] :
                          \A i \in 1..Len(seq) : g[i] \in 1..Len(seq)
                          /\ \A i, j \in 1..Len(seq) : g[i] = g[j] => i = j
                          /\ Let reordered == [i \in 1..Len(seq) |-> seq[g[i]]]
                             In FoldSeq(f, base, reordered)

\* Helper for SeqFold: fold a function over a concrete sequence.
FoldSeq(f, base, seq) == IF Len(seq) = 0 THEN base
                          ELSE f(seq[1], FoldSeq(f, base, Tail(seq)))

\* Find the index of an element in a sequence (the first occurrence).
SeqIndex(seq, x) == CHOOSE i \in 1..Len(seq) : seq[i] = x

\* Convert a sequence to the set of its elements.
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* The last element of a sequence.
SeqLast(seq) == seq[Len(seq)]

\* Test if a sequence is empty.
SeqIsEmpty(seq) == Len(seq) = 0

\* Remove all occurrences of an element from a sequence.
RemoveAll(seq, x) ==
  \* The recursive definition respects sequence order: each head is tested before
  \* recursing on the tail, so no occurrence of x can survive.
  IF Len(seq) = 0 THEN << >>
    ELSE IF seq[1] = x THEN RemoveAll(Tail(seq), x)
    ELSE << seq[1] >> \o RemoveAll(Tail(seq), x)

\* Intersection of a set of sets (the common elements of all member sets).
SetIntersection(S) == {x \in UNION S : \A Y \in S : x \in Y}

\* Generate all permutation sequences of a finite set with cardinality bounded by
\* PERMUTATIONS_MAXSIZE. The PERMUTATIONS_MAXSIZE bound exists to keep the set of
\* generated sequences finite, which is necessary for model checking.
Permutations(S) ==
  IF \E n \in Nat : n \in S /\ n > PERMUTATIONS_MAXSIZE
    THEN {}
    ELSE { seq \in Seq(S) : Len(seq) = Cardinality(S) }

\* The universe of values that may appear in a permutation.
MaxValue == {n \in 1..MAXVALUE : \E m \in PERMUTATIONS_MAXSIZE : n <= m}

\* SPECIFICATION: the top-level operator that a model checker runs. It consists of
\* the regular next-state relation, an empty initial state (no actors), and no
\* separately declared invariant or property (the operators above are utilities).
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE

\* The TLC configuration expects an INVARIANTS clause and a PROPERTIES clause even
\* though this library module has none to expose; they are defined as always true.
INVARIANTS == TRUE
PROPERTIES == TRUE

\* Test helper: given a description and a condition, prints the description on
\* failure so a failed test provides diagnostic output rather than silently passing.
TestHelper(desc, cond) == IF cond THEN TRUE ELSE (PrintT("FAIL: " \o desc); FALSE)

====