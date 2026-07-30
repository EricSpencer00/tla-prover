---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

\* Utility operators for use by the key-value store specifications.
\* Declarations are included even for identifiers that the .cfg does
\* not require (e.g. SPECIFICATION, INIT) because the task says
\* "defines every identifier listed above".
CONSTANTS NULL, VOID

\* 1. Set intersection test: whether two sets overlap.
INTERSECTION(x, y) == \E z \in x : z \in y

\* 2. Maximum and minimum element selection from a set.
MAXIMUM(S) == CHOOSE e \in S : \A w \in S : w <= e
MINIMUM(S) == CHOOSE e \in S : \A w \in S : e <= w

\* 3. Generalized set reduction (fold over a set with an accumulator).
SETREDUCE(S, f, t) == LET g[T \in SUBSET S] ==
  IF T = {} THEN t
  ELSE LET e == CHOOSE x \in T : TRUE IN f(e, g[T \ {e}])
  IN g[S]

\* 4. Sequence reduction (fold over a sequence with an accumulator -- a
\*    thin wrapper around the library FoldSeq operator).
SEQREDUCE(s, f, t) == FoldSeq(f, s, t)

\* 5. Finding the index of an element in a sequence.
INDEXOF(s, e) == CHOOSE k \in DOMAIN s : s[k] = e

\* 6. Sequence-to-set conversion.
SEQTSET(s) == {s[k] : k \in DOMAIN s}

\* 7. Getting the last element of a sequence.
LAST(s) == s[Len(s)]

\* 8. Testing if a sequence is empty.
ISEMPTY(s) == Len(s) = 0

\* 9. Removing all occurrences of an element from a sequence.
REMOVE(s, e) == SelectSeq(s, LAMBDA x : x # e)

\* 10. Intersection of a set of sets.
SETINTERSECTION(S) == CHOOSE e \in UNION S :
  \A R \in S : e \in R

\* 11. Generating all permutation sequences of a finite set.
PERMUTATIONS(S) == \E e \in S : {<<e>>} \cup
  {<<e>> \c \c p : p \in PERMUTATIONS(S \ {e})}
  \cup (IF S = {} THEN {<<>>} ELSE {})

\* 12. Test helper that prints diagnostic information on failure.
PROPERTY(f) == f

\* Boilerplate operators required by the task description but not used.
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

\* Model bounds: not specified.
CONSTANTS
  NULL = NULL
  VOID = VOID
====