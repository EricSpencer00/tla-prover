---- MODULE Util ----
EXTENDS Integers, Sequences

CONSTANTS NoResult, EmptySeq

\* Set intersection test: true iff sets s1 and s2 share at least one element.
Intersects(s1, s2) == \E x \in s1 : x \in s2

\* Maximum element of a non-empty finite set of integers.
MaxOf(s) == CHOOSE m \in s : \A y \in s : y <= m

\* Minimum element of a non-empty finite set of integers.
MinOf(s) == CHOOSE m \in s : \A y \in s : m <= y

\* Generalized reduction (fold) over a finite set s, applying function f to
\* each element and an accumulator, starting with init.
SetReduce(s, f, init) ==
  LET G[T \in SUBSET s] ==
       IF T = {} THEN init
       ELSE LET x == CHOOSE y \in T : TRUE
            IN f[x, G[T \ {x}]]
  IN G[s]

\* Reduction over a sequence using the library SeqFold operator.
SeqReduce(seq, f, init) == SeqFold(seq, f, init)

\* Find the (0-based) index of element x in sequence seq; returns -1 if absent.
SeqIndex(seq, x) ==
  LET F[i \in 0..Len(seq)] ==
       IF i = Len(seq) THEN -1
       ELSE IF seq[i + 1] = x THEN i
       ELSE F[i + 1]
  IN F[0]

\* Convert a sequence to the set of its elements, eliminating ordering/duplicates.
SeqToSet(seq) == { seq[i] : i \in 1..Len(seq) }

\* Retrieve the last element of a non-empty sequence.
SeqLast(seq) == seq[Len(seq)]

\* Test whether a sequence is empty.
SeqEmpty(seq) == Len(seq) = 0

\* Remove all occurrences of element x from a sequence, preserving order of others.
SeqRemoveAll(seq, x) ==
  [ i \in 1..(Len(seq) - Cardinality({j \in 1..Len(seq) : seq[j] = x}))
    |-> CHOOSE k \in 1..Len(seq) :
           /\ seq[k] # x
           /\ Cardinality({j \in 1..k : seq[j] # x}) = i ]

\* Intersection of a non-empty set of sets, folding pairwise intersections.
SetOfSetsIntersection(sets) == SetReduce(sets, Intersects, sets)

\* Generate every permutation of the elements of a finite set s as a sequence.
SetPermutations(s) ==
  IF s = {} THEN { << >> }
  ELSE
    UNION { [ x \in 1..Cardinality(s) |-> e ]
              : e \in s
                /\ { [ x \in 1..Cardinality(s) |-> e ] } \subseteq
                      { p \in [1..Cardinality(s) -> s] :
                         SetToSeq(SetMinus(s, { e }) \cup { e }) = p } }

\* Test helper: asserts condition cond, and on failure returns a diagnostic record.
TlaAssert(cond, msg) ==
  IF cond THEN NoResult
  ELSE [failed |-> TRUE, diagnostic |-> msg]

\* The module has no system to model directly (no actors, no actions); it only
\* provides the operators above for the other modules to use.
====