---- MODULE Util ----
EXTENDS Naturals, Sequences

CONSTANTS S, T, U, V

\* Intersection: true iff two sets have a common element.
Intersect(a, b) == \E x \in a : x \in b

\* Fold over a set with an accumulator, applying f to each element.
FoldSet(f, s, a) == IF s = {} THEN a
                    ELSE LET x == CHOOSE y \in s : TRUE
                         IN f[x, FoldSet(f, s \ {x}, a)]

\* Sequence reduction: fold a binary function left-to-right over a seq.
FoldSeq(f, seq, a) == IF seq = <<>> THEN a
                      ELSE f[Head(seq), FoldSeq(f, Tail(seq), a)]

\* Find the 1-based index of an element in a sequence (or 0 if absent).
IndexOf(seq, e) ==
  LET g[S \in Seq(T)] == IF S = <<>> THEN 0
                         ELSE IF Head(S) = e THEN 1
                         ELSE IF IndexOf(Tail(S), e) = 0 THEN 0
                         ELSE 1 + IndexOf(Tail(S), e)
  IN g[seq]

\* Convert a sequence to the set of the elements it visits.
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* Permutations of a finite set, using a standard recursive scheme.
Permutations(s) ==
  IF s = {} THEN { <<>> }
  ELSE { <<x>> \o p : x \in s, p \in Permutations(s \ {x}) }

\* Helper that prints diagnostic context when an assertion fails.
Assert(p, msg) == IF p THEN TRUE ELSE msg

\* The module's required exports: no state, so every exported name is a constant.
CONSTANTS
  Intersect, FoldSet, FoldSeq, IndexOf,
  SeqToSet, Permutations, Assert,
  S, T, U, V

Spec == TRUE
Init == TRUE
Next == TRUE
Invariants == {}
Properties == {}

====