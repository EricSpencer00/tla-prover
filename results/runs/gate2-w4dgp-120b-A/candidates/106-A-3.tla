---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* Utility functions for set and sequence manipulation.  Since this module has
\* no actors and no state it does not have a SPECIFICATION section; it only
\* provides reusable operators for other modules to import.

NoActors == TRUE

\* Intersection: two sets share an element iff some element belongs to both.
SetsIntersect(a, b) == \E x \in a : x \in b

\* Extrema: maximum and minimum element of a non-empty ordered set.
SetMaximum(S) == CHOOSE e \in S : \A f \in S : f <= e
SetMinimum(S) == CHOOSE e \in S : \A f \in S : e <= f

\* Generalized reduction over a set via pairwise folding on an accumulator.
SetFold(f, S, base) == LET
  rec[T \in SUBSET S] ==
    IF T = {} THEN base
    ELSE \E x \in T : f(x, rec[T \ {x}])
  IN rec[S]

\* Reduction over a sequence, using the built-in foldl operator.
SeqFold(f, seq, base) == FoldL(f, seq, base)

\* Find the index of an element in a sequence (1-indexed), or 0 if absent.
SeqIndex(seq, v) == LET
  rec[i \in 0..Len(seq)] ==
    IF i = 0 THEN 0
    ELSE IF seq[i] = v THEN i
    ELSE rec[i - 1]
  IN rec[Len(seq)]

\* Convert a sequence to the set of its elements.
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* The last element of a sequence; undefined for the empty sequence.
SeqLast(seq) == seq[Len(seq)]

SeqEmpty(seq) == Len(seq) = 0

SeqRemoveAll(seq, v) ==
  IF seq = <<>> THEN seq
  ELSE IF Head(seq) = v THEN SeqRemoveAll(Tail(seq), v)
  ELSE <<Head(seq)>> \o SeqRemoveAll(Tail(seq), v)

\* Intersection of a set of sets.
SetOfSetsIntersection(S) ==
  CHOOSE b \in S : \A a \in S : a \subseteq b

\* All permutations of a finite set, given as sequences.
SetPermutations(S) ==
  LET
    rec[T \in SUBSET S] ==
      IF T = {} THEN { <<>> }
      ELSE { <<x>> \o s : x \in T, s \in rec[T \ {x}] }
  IN rec[S]

\* Test helper: asserts a condition, printing a message on failure.
\* Write a comment on the line before an invocation to explain what failed
\* if the model ever hits this.
Assert(p) == IF p THEN TRUE ELSE Print("Assertion failed"); FALSE
====