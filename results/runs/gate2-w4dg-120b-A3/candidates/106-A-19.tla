---- MODULE Util ----
EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS MaxSeq, MaxVal

\* Set intersection: true exactly when s and t share at least one element.
Intersect(s, t) == \E x \in s : x \in t

\* Maximum element of a non-empty set, via reduction; MinElem for the smallest.
Reduce(s, r, init) ==
  LET f[T \in SUBSET s] ==
    IF T = {} THEN init
    ELSE LET x == CHOOSE y \in T : TRUE IN r(x, f[T \ {x}])
  IN f[s]

MaxElem(s) == Reduce(s, LAMBDA x, y : IF x > y THEN x ELSE y, -1)
MinElem(s) == Reduce(s, LAMBDA x, y : IF x < y THEN x ELSE y, MaxVal + 1)

\* Sequence reduction: fold an operator over the sequence of elements.
SeqReduce(seq, r, init) == Fold(r, init, seq)

\* Find the index of element x in sequence seq (1-indexed), or 0 if absent.
SeqIndex(seq, x) == IF x \in SeqSet(seq) THEN CHOOSE k \in DOMAIN seq : seq[k] = x ELSE 0

SeqSet(seq) == { seq[k] : k \in DOMAIN seq }

Last(seq) == seq[Len(seq)]

SeqEmpty(seq) == Len(seq) = 0

\* Remove all instances of element x from a sequence.
SeqRemove(seq, x) == SelectSeq(seq, LAMBDA y : y # x)

\* Intersection of a set of sets: the elements common to every member set.
SetIntersect(S) == { x \in UNION S : \A t \in S : x \in t }

\* Convert a set into the set of all its permutations as sequences.
Permutations(s) ==
  IF s = {} THEN { << >> }
  ELSE { << x >> \circ seq : x \in s, seq \in Permutations(s \ {x}) }

\* Assertion helper that prints a counterexample and fails the spec when false.
Check(pred, msg) ==
  IF pred THEN TRUE ELSE (Print(msg); FALSE)

Spec == TRUE
Init == TRUE
Next == TRUE
INVARIANTS == TRUE
CONSTANTS == TRUE

====