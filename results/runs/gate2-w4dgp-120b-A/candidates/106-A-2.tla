---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

\* Set intersection: true iff sets s and t share at least one element.
Intersect(s, t) == \E x \in s : x \in t

\* Maximum element of a non-empty set.
SetMaximum(s) == CHOOSE m \in s : \A x \in s : x <= m

\* Minimum element of a non-empty set.
SetMinimum(s) == CHOOSE m \in s : \A x \in s : m <= x

\* Generalized set reduction: fold a binary operator g over a set s, starting
\* with identity element e. Order is nondeterministic but reduction is associative
\* if the operator is, so the result is well-defined.
SetFold(g, e, s) == LET
  recurse[T \in SUBSET s] ==
    IF T = {} THEN e
    ELSE \E x \in T : g[x, recurse[T \ {x}]]
  IN recurse[s]

\* Sequence reduction: fold a binary operator g over the elements of a
\* sequence s, left to right, using the library FoldSeq operator.
SeqFold(g, e, s) == FoldSeq(g, s, e)

\* Find the index (1-based) of element x in sequence s; 0 if not present.
SeqIndex(s, x) == IF x \notin {s[i] : i \in 1..Len(s)} THEN 0
                  ELSE CHOOSE i \in 1..Len(s) : s[i] = x

\* Convert a sequence to the set of its elements.
SeqToSet(s) == {s[i] : i \in 1..Len(s)}

\* The last element of a non-empty sequence.
SeqLast(s) == s[Len(s)]

\* Empty-sequence predicate.
SeqEmpty(s) == Len(s) = 0

\* Remove all occurrences of element x from sequence s.
SeqRemoveAll(s, x) == [i \in 1..(Len(s) - Cardinality({j \in 1..Len(s) : s[j] = x}))
                         |-> IF i < SeqIndex(s, x) THEN s[i]
                            ELSE s[i + Cardinality({j \in 1..Len(s) : s[j] = x})]]

\* Intersection of a set of sets: elements common to every member.
SetOfSetsIntersection(S) == {x \in UNION S : \A t \in S : x \in t}

\* Generate all permutations of a finite set s as sequences.
Permutations(s) ==
  LET
    recurse[T \in SUBSET s] ==
      IF T = {} THEN << >>
      ELSE {<< x >> \o p : x \in T, p \in recurse[T \ {x}] }
  IN recurse[s]

\* Test helper: assert condition c, print a diagnostic on failure.
Assert(c) == IF c THEN TRUE ELSE (Print("Assertion failed"); FALSE)

====