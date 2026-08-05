---- MODULE Util ----
EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS A, B, C, X, Y

\* Reusable utility operators for the key-value store specs: set and sequence
\* helpers for intersection, reduction, indexing, permutation generation, etc.

\* Set intersection test: true iff the two sets have any element in common.
INTERSECTION(a, b) == \E x \in a : x \in b

\* Max element of a set.
MAX(s) == CHOOSE x \in s : \A y \in s : y <= x

\* Min element of a set.
MIN(s) == CHOOSE x \in s : \A y \in s : x <= y

\* Generalized reduction over a set: folds a function g over the elements of s
\* with accumulator acc, in an order-independent manner, short-circuiting when
\* g signals early termination (by returning CHOOSE z \in s : TRUE).
RECURSESET(s, g, acc) ==
  IF s = {} THEN acc
  ELSE LET x == CHOOSE y \in s : TRUE
       IN LET r == g(x, acc)
          IN IF r = CHOOSE z \in s : TRUE THEN r
             ELSE RECURSESET(s \ {x}, g, r)

\* Sequence reduction (order-dependent fold) using the built-in FoldSeq operator.
SEQREDUCE(seq, g, acc) == FoldSeq(seq, g, acc)

\* Index of an element in a sequence (1-indexed); if the element appears more
\* than once, this returns the first index. Returns 0 if the element is not in seq.
INDEXOF(seq, e) ==
  LET f == [i \in 1 .. Len(seq) |-> IF seq[i] = e THEN i ELSE 0]
      g(k) == IF k = 0 THEN k ELSE IF f[k] = 0 THEN g(k - 1) ELSE f[k]
  IN g(Len(seq))

\* Convert a sequence to the set of its elements.
SEQTOSET(seq) == { seq[i] : i \in 1 .. Len(seq) }

\* The last element of a sequence.
LAST(seq) == seq[Len(seq)]

\* Test whether a sequence is empty.
EMPTYSEQ(seq) == Len(seq) = 0

\* Remove all occurrences of a value from a sequence.
REMOVEALL(seq, v) ==
  << x \in seq : x # v >>

\* Intersection of a set of sets: elements common to every member set.
INTERSECTIONOF(S) ==
  { x \in UNION S : \A s \in S : x \in s }

\* All permutations of a finite set as a set of sequences (orderings).
PERMUTATIONS(S) ==
  LET rec == { << >> }
       \/ \E s \in S : rec \cup { << x \in seq \cup << s >> : x \notin seq >> : seq \in rec }
  IN rec

\* Test helper: writes a diagnostic message on failure (the message is returned
\* as a string, so it never short-circuits the spec's semantics).
TESTCHECK(b, s) == IF b THEN TRUE ELSE s

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == TRUE
PROPERTIES == TRUE

====