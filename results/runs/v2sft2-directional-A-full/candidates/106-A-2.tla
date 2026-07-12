---- MODULE Util ----
EXTENDS Sequences, SET, NatSet, Print

\* ----------------------------------------------------------------------
\* Utility operators for the key-value store specifications
\* ----------------------------------------------------------------------


\* Test whether two sets overlap (i.e., their intersection is non-empty)
Overlaps(A, B) == A \cap B # {}

\* Maximum element of a finite set of natural numbers
MaxElem(S) == Max(S)

\* Minimum element of a finite set of natural numbers
MinElem(S) == Min(S)

\* Generic set fold (fold over a set with an accumulator).  The function
\* f must be associative (or the caller must accept nondeterminism for
\* non‑associative f).
SetFold(f, init, S) ==
  IF S = {} THEN init
  ELSE
    LET x \in S IN
      f(x, SetFold(f, init, S \ {x}))

\* Sequence fold (fold over a sequence with an accumulator)
SeqFold(f, init, seq) == Fold(f, init, seq)

\* Find the first index (1‑based) of element e in sequence seq; 0 if not found
FindIndex(seq, e) == Index(seq, e)

\* Convert a sequence into the set of its elements
SeqToSet(seq) == SetOf(seq)

\* Get the last element of a non‑empty sequence
LastElem(seq) == Last(seq)

\* Test if a sequence is empty
IsEmpty(seq) == seq = []

\* Remove all occurrences of element e from a sequence
RemoveAll(seq, e) ==
  IF seq = [] THEN []
  ELSE IF Head(seq) = e THEN RemoveAll(Tail(seq), e)
  ELSE Head(seq) \o RemoveAll(Tail(seq), e)

\* Compute the intersection of a set of finite sets
SetIntersectionAll(sets) == Intersection(sets)

\* Generate the set of all permutation sequences of a finite set S
Permutations(S) ==
  IF S = {} THEN { <<>> }
  ELSE { e \o P \mid e \in S & P \in Permutations(S \ {e}) }

\* Test helper that prints diagnostic information on failure
Assert(p) ==
  IF p THEN TRUE ELSE (Print("Assertion failed: ", p); FALSE)

====