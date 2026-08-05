---- MODULE Util ----
EXTENDS Naturals, Sequences

\* Set intersection: true iff the two argument sets share at least one element.
SetIntersection(S, T) == \E x \in S : x \in T

\* Select the maximum element of a non-empty set.
SetMaximum(S) == CHOOSE mx \in S : \A x \in S : x <= mx

\* Select the minimum element of a non-empty set.
SetMinimum(S) == CHOOSE mn \in S : \A x \in S : mn <= x

\* Generalized set reduction: applies a binary accumulator function over the set.
SetReduce(S, f, init) ==
  LET rec[T \in SUBSET S] ==
    IF T = {} THEN init
    ELSE LET x == CHOOSE y \in T : TRUE IN f[x, rec[T \ {x}]]
  IN rec[S]

\* Sequence reduction: applies a binary accumulator function over a sequence.
SeqReduce(seq, f, init) == Reduce(f, seq, init)

\* Finds the 1-based index of element x in the sequence seq, or 0 if not present.
SeqIndexOf(seq, x) ==
  LET rec(k) ==
    IF k > Len(seq) THEN 0
    ELSE IF seq[k] = x THEN k ELSE rec(k + 1)
  IN rec(1)

\* The set of distinct elements occurring in a sequence.
SeqToSet(seq) == { seq[k] : k \in 1..Len(seq) }

\* The last element of a non-empty sequence.
SeqLast(seq) == seq[Len(seq)]

\* Checks whether a sequence is empty.
IsSeqEmpty(seq) == Len(seq) = 0

\* Removes all occurrences of element x from a sequence.
SeqRemove(seq, x) ==
  LET rec(k) ==
    IF k > Len(seq) THEN << >>
    ELSE IF seq[k] = x THEN rec(k + 1) ELSE << seq[k] >> \o rec(k + 1)
  IN rec(1)

\* Intersection of a set of sets (empty intersection defaults to the universe).
SetSetIntersection(S) ==
  IF S = {} THEN {}
  ELSE LET rec(T) ==
         IF T = {} THEN CHOOSE x \in S : TRUE
         ELSE LET x == CHOOSE y \in S : TRUE IN x \cap rec(T \ {x})
       IN rec(S)

\* Generates all permutation sequences of the finite set S.
SetPermutations(S) ==
  LET rec(T) ==
    IF T = {} THEN { << >> }
    ELSE { << x >> \o p : x \in T, p \in rec(T \ {x}) }
  IN rec(S)

\* Test helper: fails with a diagnostic message if the condition is false.
Assert(cond, msg) == IF cond THEN TRUE ELSE (Print(msg); FALSE)

====