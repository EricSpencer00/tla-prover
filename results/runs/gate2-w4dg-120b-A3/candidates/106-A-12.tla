---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS MaxCardinality

\* Intersection test: whether two sets have any element in common.
Intersects(f, g) == \E x \in f : x \in g

\* Maximum over a non-empty set; MINSET over a non-empty set.
\* These are the standard set reductions over the order given by the
\* naturals' built-in ordering.
MAXSET(f) == CHOOSE x \in f : \A y \in f : y <= x
MINSET(f) == CHOOSE x \in f : \A y \in f : x <= y

\* Generalized reduction (fold) over a set, with an accumulator and a binary
\* operation op (for example op = +).  The accumulator starts at init.
FoldSet(f, init, op) ==
  LET g[S \in SUBSET f] ==
        IF S = {} THEN init
        ELSE LET x == CHOOSE y \in S : TRUE
                 rest == g[S \ {x}]
             IN op[x, rest]
  IN g[f]

\* Sequence reduction (fold left) over a sequence, using the library function
\* FoldSeq from the Sequences module.  This is the counterpart of FoldSet.
FoldSeq(s, init, op) == FoldSeq(s, init, op)

\* Index of an element in a sequence (1-indexed, as TLA+ sequences are).
Idx(s, x) == CHOOSE i \in DOMAIN s : s[i] = x

\* Convert a sequence to the set of its elements.
SeqToSet(s) == {s[i] : i \in DOMAIN s}

\* The last element of a non-empty sequence.
Last(s) == s[Len(s)]

\* Test for an empty sequence.
IsEmptySeq(s) == s = << >>

\* Remove all occurrences of a given element from a sequence.
RemoveAll(s, x) ==
  [i \in 1..Cardinality({k \in DOMAIN s : s[k] # x}) |-> s[CHOOSE k \in DOMAIN s : s[k] # x /\ Card({j \in DOMAIN s : s[j] # x /\ j < k}) = i - 1]]

\* Intersection of a set of sets.
IntersectSetOfSets(S) ==
  IF S = {} THEN {}
  ELSE {x \in UNION S : \A Y \in S : x \in Y}

\* Generate all permutations of a finite set f; the result is a set of
\* sequences, each of which is a permutation of f's elements.
Permutations(f) ==
  IF f = {} THEN {}
  ELSE LET p[g \in SUBSET f] ==
          IF g = {} THEN {}
          ELSE IF Cardinality(g) = 1 THEN {<<CHOOSE x \in g : TRUE>>}
          ELSE {<<x>> \o s : x \in g /\ s \in p[g \ {x}]}
       IN p[f]

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE
====