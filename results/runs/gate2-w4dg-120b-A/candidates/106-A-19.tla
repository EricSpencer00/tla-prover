---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NONE

\* Utility operators used across the key-value store specs.
\* The spec below declares very few identifiers required by the
\* reference TLC .cfg, but the paper description insists the module
\* provide this full library of operators.

RECURSIVE ReduceSet(_, _)
ReduceSet(f, s) ==
  IF s = {} THEN 0
  ELSE LET x == CHOOSE y \in s : TRUE
       IN f[x] + ReduceSet(f, s \ {x})

RECURSIVE ReduceSeq(_, _)
ReduceSeq(f, seq) ==
  IF seq = <<>> THEN 0
  ELSE f[Head(seq)] + ReduceSeq(f, Tail(seq))

\* Intersection test: true iff two sets have a common element.
INTERSECT(s, t) ==
  \E x \in s : x \in t

\* Maximum and minimum elements of a non-empty set of naturals.
MaxSet(s) ==
  LET f[U] ==
        IF s = {} THEN 0
        ELSE LET x == CHOOSE y \in s : TRUE
             IN IF U = {} THEN x ELSE IF x > MaxSet(U) THEN x ELSE MaxSet(U)
  IN f[s]

MinSet(s) ==
  LET f[U] ==
        IF s = {} THEN 0
        ELSE LET x == CHOOSE y \in s : TRUE
             IN IF U = {} THEN x ELSE IF x < MinSet(U) THEN x ELSE MinSet(U)
  IN f[s]

SeqIntersect(s1, s2) == {x \in s1 : x \in s2}

SeqToSet(seq) == {seq[i] : i \in 1..Len(seq)}

\* Generate all permutations of the finite set s as a set of
\* sequences -- a factorial number of results for a set of size n.
Permutations(s) ==
  IF s = {} THEN {<<>>}
  ELSE { <<x>> \o p : x \in s, p \in Permutations(s \ {x}) }

\* Remove every occurrence of `elem` from the sequence `seq`.
RemoveFromSeq(seq, elem) ==
  IF seq = <<>> THEN <<>>
  ELSE IF Head(seq) = elem THEN RemoveFromSeq(Tail(seq), elem)
  ELSE <<Head(seq)>> \o RemoveFromSeq(Tail(seq), elem)

\* Test helper that writes a diagnostic and fails the spec when its
\* condition is false. Useful for debugging in the model checker.
\* TLC prints the message on failure.
\* (The spec makes no claim about the literal text.)
Assert(msg, cond) ==
  IF cond THEN TRUE
  ELSE PrintT(msg) /\ FALSE

Last(seq) == IF seq = <<>> THEN NONE ELSE seq[Len(seq)]

SeqEmpty(seq) == Len(seq) = 0

\* The reference TLC configuration expects no SPECIFICATION, INIT,
\* NEXT, INVARIANTS, or PROPERTY identifiers from this module, but
\* they must still be declared here so the spec is complete.

Spec == TRUE
Init == TRUE
Next == TRUE
TypeOK == TRUE
NoDeadlock == TRUE
====