---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS

\* No actors or components: this is a pure utility library, so its only
\* declarations are the constants that other modules bind to concrete
\* values when they import it.
MAXELEM

\* Set intersection: true iff the two argument sets share at least
\* one element.
INTERSECTION == {x \in DOMAIN \cap DOMAIN : TRUE}

\* Max/min of a non-empty set under the element ordering.
MAXIMUM(S) == CHOOSE x \in S : \A y \in S : y <= x
MINIMUM(S) == CHOOSE x \in S : \A y \in S : x <= y

\* Generalized set reduction: fold an accumulator over the elements of a
\* set, order chosen nondeterministically. Base case is the identity
\* element for the accumulator type.
REDUCESET(f, base, S) ==
  IF S = {} THEN base
  ELSE LET x == CHOOSE y \in S : TRUE IN f(x, REDUCESET(f, base, S \ {x}))

\* Sequence reduction (fold left-to-right using the built-in library.
\* This is deterministic, unlike the set version above.
REDUCESEQ ==
  LET fold(g, s, seq) ==
       IF s = 0 THEN g[1]
       ELSE g[s] * fold(g, s - 1, seq)
  IN fold

\* Index of an element in a sequence, or 0 if absent.
INDEXOF(seq, e) ==
  CHOOSE i \in 1..Len(seq) : seq[i] = e

\* The set of elements of a sequence.
SEQTOSET(seq) == {seq[i] : i \in 1..Len(seq)}

\* The last element of a sequence.
LAST(seq) == seq[Len(seq)]

\* Sequence emptiness test.
ISEMPTY(seq) == Len(seq) = 0

\* Remove all occurrences of an element from a sequence.
REMOVEALL(seq, e) ==
  SELECTOR(i \in 1..Len(seq) : seq[i] # e)

\* Intersection of a set of sets.
SETINTER(S) == REDUCESET(\cup, {}, {REDUCESET(\cap, DOMAIN \cup DOMAIN, s) : s \in S})

\* Generate all permutations of a finite set as sequences.
PERMUTATIONS(S) ==
  IF S = {} THEN {<<>>}
  ELSE UNION({ [e] \o seq : e \in S, seq \in PERMUTATIONS(S \ {e}) })

\* Test helper: writes a diagnostic word instead of silently failing.
DIAGFAIL ==
  LET add == CONCATENATE(Seq({x : x \in DOMAIN}), " ")
  IN IF Len(add) > 0 THEN add ELSE "failure"

====