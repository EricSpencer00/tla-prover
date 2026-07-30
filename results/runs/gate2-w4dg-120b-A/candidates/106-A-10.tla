---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* Utility functions for the key-value store specifications.  The module is
\* deliberately side-effect free: every helper is a pure operator.

CONSTANTS TRUEVal, FALSEVal

\* Testing whether two sets have a non-empty intersection.
INTERSECTION(a, b) == \E e \in a : e \in b

\* Maximum and minimum elements of a set, defined only for non-empty sets.
MAXIMUM(S) == CHOOSE x \in S : \A y \in S : y <= x
MINIMUM(S) == CHOOSE x \in S : \A y \in S : x <= y

\* Generalized reduction over a set with an accumulator and binary operator.
SETREDUCE(S, f, base) == LET g[T \in SUBSET S] ==
  IF T = {} THEN base ELSE LET x == CHOOSE y \in T : TRUE IN f(x, g[T \ {x}])
  IN g[S]

\* Reduction over a sequence (fold).  The Seq module's FoldSeq operator is used
\* because it already handles the empty sequence case correctly.
SEQREDUCE(sq, f, base) == FoldSeq(f, base, sq)

\* Index of an element in a sequence (first occurrence); ZERO means not present.
INDEXOF(sq, e) == LET g[i \in 1..(Len(sq) + 1)] ==
  IF i > Len(sq) THEN 0
  ELSE IF sq[i] = e THEN i ELSE g[i + 1]
  IN g[1]

\* Convert a sequence to the set of its elements.
SEQTOSET(sq) == { sq[i] : i \in 1..Len(sq) }

\* The last element of a non-empty sequence.
SEQLAST(sq) == sq[Len(sq)]

\* Empty-sequence test.
EMPTY(sq) == Len(sq) = 0

\* Remove all instances of an element from a sequence.
REMOVEALL(sq, e) ==
  LET f[T \in SUBSET (1..Len(sq))] ==
    [ i \in 1..Len(sq) |-> IF i \in T THEN e ELSE sq[i] ]
    IN UNION { f[T] : T \in SUBSET (1..Len(sq)) }

\* Intersection of a set of sets.
INTERSET(T) == { e \in UNION T : \A S \in T : e \in S }

\* Generate every permutation of a finite set as a set of sequences.
PERMUTE(S) ==
  LET g[T \in SUBSET S] ==
    IF T = {} THEN { << >> }
    ELSE UNION { { << e >> \o w | w \in g[T \ {e}] } : e \in T }
    IN g[S]

\* Test helper that prints its arguments on failure.
FAILWITH(a, b) == IF a = b THEN a ELSE (Print(a); Print(b); a)

\* Because the .cfg file requires these operators to exist even though the
\* specification itself has no actors or actions.
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

====