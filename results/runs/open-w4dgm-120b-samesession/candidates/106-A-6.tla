---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS None

\* Intersection test: True iff the two sets share at least one element.
Intersect(a, b) == \E x \in a : x \in b

\* Generalized reduction (fold) over a set of integer elements with an accumulator.
ReduceSet(f, S, e) == IF S = {} THEN e
                     ELSE LET x == CHOOSE y \in S : TRUE
                          IN ReduceSet(f, S \ {x}, f[x, e])

\* Reduction over a sequence via a library foldl operator.
ReduceSeq(f, seq, e) == FoldSeq(f, seq, e)

\* Find the index of element x in the (non-empty) sequence seq, or 0 if absent.
SeqIndex(x, seq) ==
  IF seq = <<>> THEN 0
  ELSE IF Head(seq) = x THEN 1
  ELSE LET i == SeqIndex(x, Tail(seq))
       IN IF i = 0 THEN 0 ELSE i + 1

SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* Recursive permutation generator: length-n permutations of the given set.
PermutationsOf(S) ==
  IF S = {} THEN {<<>>}
  ELSE {<<x>> \o p : x \in S, p \in PermutationsOf(S \ {x})}

\* Helper that prints a diagnostic message before asserting a condition.
Require(msg, P) == IF P THEN TRUE ELSE (Print(msg); FALSE)

====