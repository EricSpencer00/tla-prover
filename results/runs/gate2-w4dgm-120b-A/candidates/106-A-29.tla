---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nums

\* Set-intersection test: two sets overlap if their intersection is non-empty.
Intersect(s, t) == Cardinality(s \cap t) > 0

\* Reduction (fold) over a set: combine elements using a binary operator with an
\* accumulator, order of combination is nondeterministic (commutative reduction).
SetFold(f, S, a) ==
  IF S = {} THEN a
  ELSE \E x \in S : SetFold(f, S \ {x}, f[a, x])

\* Reduction (fold) over a sequence: combine elements from left to right using
\* a binary operator with an accumulator.
SeqFold(f, seq) == FoldSeq(f, seq)

\* Find the index of element x in sequence seq; 0 indicates x not present.
SeqIndex(seq, x) ==
  CHOOSE i \in DOMAIN seq : seq[i] = x
    OTHERWISE 0

\* Convert a sequence to the set of its elements (order is discarded).
SeqToSet(seq) == {seq[i] : i \in DOMAIN seq}

\* Return the last element of a non-empty sequence.
SeqLast(seq) == seq[Len(seq)]

\* Test whether a sequence is empty.
SeqEmpty(seq) == Len(seq) = 0

\* Remove all occurrences of element x from a sequence.
SeqRemove(seq, x) ==
  IF seq = <<>> THEN seq
  ELSE IF Head(seq) = x THEN SeqRemove(Tail(seq), x)
  ELSE <<Head(seq)>> \o SeqRemove(Tail(seq), x)

\* Intersection of a set of sets.
SetIntersections(sets) ==
  LET g[S \in SUBSET sets] ==
        IF S = {} THEN UNION sets
        ELSE LET x == CHOOSE y \in S : TRUE IN g[S \ {x}] \cap x
  IN g[sets]

\* All permutations of a finite set of numbers as sequences.
Permutations ==
  LET f[T \in SUBSET Nums] ==
        IF T = {} THEN {<<>>}
        ELSE { <<x>> \o p : p \in f[T \ {x}] } @@ x \in T
  IN f[Nums]

\* Test helper: asserts a condition and prints diagnostic failure info.
Assert(cond, msg) == IF cond THEN "ok" ELSE ~msg

====