---- MODULE Util ----
EXTENDS Integers, FiniteSets, Sequences, TLC

\* Utility operators reused across the key-value store specifications.
\* Not a system: no actors, no variables, and no INVARIANT/PROPERTY to check
\* at the top level.  It only exports pure functions.

\* 1. set intersection test: true iff the two sets overlap
INTERSECTS(S, T) == \E x \in S : x \in T

\* 2. maximum/minimum element of a finite non-empty set (guarded by \E x \in S)
MAX(S) == CHOOSE x \in S : \A y \in S : y <= x
MIN(S) == CHOOSE x \in S : \A y \in S : y >= x

\* 3. generalized set reduction (fold over a set with an accumulator)
REDEX(F, S, a) == IF S = {} THEN a
                  ELSE LET x == CHOOSE y \in S : TRUE
                       IN REDEX(F, S \ {x}, F[a, x])

\* 4. sequence reduction (fold over a sequence with an accumulator)
REDSEQ(F, seq) == Reduces(seq, F)
Reduces(seq, F) ==
  LET f[k \in 1..Len(seq)] == IF k = 0 THEN seq[1]
                              ELSE F[f[k - 1], seq[k]] IN f[Len(seq)]

\* 5. index of an element in a sequence (returns 0 if not present)
INDEXOF(seq, x) ==
  LET g[k \in 1..Len(seq)] ==
        IF seq[k] = x THEN k
        ELSE IF k = 1 THEN 0 ELSE g[k - 1] IN g[Len(seq)]

\* 6. convert a sequence into the set of its elements
SEQTOSET(seq) == {seq[k] : k \in 1..Len(seq)}

\* 7. the last element of a sequence
LAST(seq) == seq[Len(seq)]

\* 8. empty-sequence predicate
ISEMPTY(seq) == Len(seq) = 0

\* 9. remove all occurrences of an element from a sequence
REMOVEALL(seq, x) ==
  IF seq = <<>> THEN <<>>
  ELSE IF Head(seq) = x THEN REMOVEALL(Tail(seq), x)
  ELSE <<Head(seq)>> \o REMOVEALL(Tail(seq), x)

\* 10. intersection of a set of sets
INTERSECTIONOF(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE IN x \cap INTERSECTIONOF(S \ {x})

\* 11. all permutation sequences of a finite set
PERMUTATIONS(S) ==
  IF S = {} THEN {<<>>}
  ELSE { <<x>> \o s : x \in S, s \in PERMUTATIONS(S \ {x}) }

\* 12. test helper that prints a message on failure (no effect on spec semantics)
HARDER == TRUE
WHICH(v) ==
  IF HARDER THEN PrintT("FAILURE:", v); v
  ELSE v

====