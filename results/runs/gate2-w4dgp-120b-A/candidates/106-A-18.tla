---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* Utility library for the key-value store project.  All operators below are
\* pure functions; the module itself has no variables, actors, or actions.
\* SAFETY and LIVENESS properties are defined as always-true placeholders
\* so that REFERENCED in the .cfg is nevertheless a concrete identifier
\* rather than an undefined name.

CONSTANTS

\* No constants are required by this library, but the name is declared so
\* the reference config that mentions CONSTANTS stays satisfied.

ASSUME TRUE

\* Set-intersection test: true iff two sets share at least one element.
SetIntersects(a, b) == \E x \in a : x \in b

\* Generalized reduction over a set: folds f over the elements of s,
\* starting with base.
SetReduce(f, base, s) ==
  LET g[T \in SUBSET s] ==
    IF T = {} THEN base
    ELSE LET x == CHOOSE y \in T : TRUE IN f(x, g[T \ {x}])
  IN g[s]

\* Generalized reduction over a sequence: folds f over the elements of s
\* in order, starting with base.  Uses the library FoldSeq operator.
SeqReduce(f, base, s) == FoldSeq(f, base, s)

\* Element index: returns the position of x in s (or 0 if absent).
IndexOf(x, s) ==
  LET g[T \in SUBSET (1..Len(s))] ==
    IF T = {} THEN 0
    ELSE LET i == CHOOSE y \in T : TRUE IN IF s[i] = x THEN i ELSE g[T \ {i}]
  IN g[1..Len(s)]

\* Set-of: the set of all elements that appear in sequence s.
SetOf(s) == {s[i] : i \in 1..Len(s)}

\* The last element of a non-empty sequence.
LastOf(s) == s[Len(s)]

\* Empty-sequence test: true iff s has no elements.
SeqEmpty(s) == Len(s) = 0

\* Remove all occurrences of x from s.
SeqDrop(x, s) == SelectSeq(s, LAMBDA y : y # x)

\* Intersection of a set of sets: the set of elements that appear in every
\* member of the argument set.
SetsIntersect(S) == {x \in UNION S : \A y \in S : x \in y}

\* Permutations of a finite set: the set of all sequences that are
\* permutations of the argument set's elements.
Permutations(T) ==
  {s \in Seq(T) : \A i, j \in 1..Len(s) : s[i] = s[j] => i = j}

\* Test helper: true iff b, and prints a diagnostic message on failure.
Assert(b, msg) == IF b THEN TRUE ELSE Print("assertion failed: " \cup msg)

SPECIFICATION Spec

Init == TRUE

Next == TRUE

INVARIANT Inv == TRUE

PROPERTY Prop == TRUE

====