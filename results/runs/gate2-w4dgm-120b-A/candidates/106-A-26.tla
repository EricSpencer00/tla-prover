---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS SeqBound

\* Utility operators shared by the key-value store specs.
\* (1) Set intersection: true iff two sets overlap.
SetIntersect(a, b) == \E x \in a : x \in b

\* (2) Max/min element of a non-empty set.
SetMax(a) == CHOOSE x \in a : \A y \in a : y <= x
SetMin(a) == CHOOSE x \in a : \A y \in a : x <= y

\* (3) Generalized reduction (fold) over a set with an accumulator.
ReduceSet(f, base, a) ==
  LET g[S \in SUBSET a] ==
        IF S = {} THEN base
        ELSE LET x == CHOOSE y \in S : TRUE
             IN f(x, g[S \ {x}])
  IN g[a]

\* (4) Sequence reduction via a library fold operator.
ReduceSeq(f, base, seq) == FoldSeq(f, base, seq)

\* (5) Find the index of an element in a sequence; 0 if absent.
IndexOf(seq, x) == CHOOSE i \in 1..Len(seq) : seq[i] = x

\* (6) Convert a sequence to the set of its elements.
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* (7) Get the last element of a non-empty sequence.
SeqLast(seq) == seq[Len(seq)]

\* (8) Sequence emptiness test.
SeqEmpty(seq) == Len(seq) = 0

\* (9) Remove all occurrences of a value from a sequence.
RemoveAll(seq, val) ==
  IF seq = <<>> THEN <<>>
  ELSE IF Head(seq) = val THEN RemoveAll(Tail(seq), val)
  ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), val)

\* (10) Intersection of a set-of-sets.
SetIntersection(ss) == ReduceSet(SetIntersect, {}, ss)

\* (11) Generate all permutation sequences of a finite set.
Permutations(set) ==
  LET pick[S \in SUBSET set] ==
        IF S = {} THEN {}
        ELSE { <<x>> \o s : x \in S, s \in pick[S \ {x}] }
  IN pick[set]

\* (12) Test helper: asserts a condition and prints a diagnostic (no-op here).
Assert(cond) == cond

\* No-system constants block -- required by the .cfg but empty here.
CONSTANTS == {}

Spec == TRUE
Init == TRUE
Next == TRUE
TypeOK == TRUE
SpecBound == TRUE

====