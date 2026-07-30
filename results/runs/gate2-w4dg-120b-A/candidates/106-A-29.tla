---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS NONE

\* A utility library module for the key-value store specs. It defines reusable
\* operators on sets and sequences, and its own (empty) spec so the .cfg can
\* refer to SPECIFICATION, INVARIANT, and PROPERTY names.

\* Set intersection test: whether two sets overlap.
Overlap(s1, s2) == \E x \in s1 : x \in s2

\* Maximum and minimum (choose by the Naturals ordering; NONE for an empty set).
SetMax(s) == IF s = {} THEN NONE ELSE CHOOSE x \in s : \A y \in s : y <= x
SetMin(s) == IF s = {} THEN NONE ELSE CHOOSE x \in s : \A y \in s : x <= y

\* Generalized reduction over a set with an accumulator.
SetReduce(s, f, z) == LET g[T \in SUBSET s] ==
                         IF T = {} THEN z
                         ELSE LET x == CHOOSE y \in T : TRUE
                              IN f(x, g[T \ {x}])
                     IN g[s]

\* Reduction over a sequence with an accumulator, using the library FoldSeq.
SeqReduce(seq, f, z) == FoldSeq(seq, z, f)

\* Find the index of an element in a sequence.
SeqIndex(seq, e) == CHOOSE i \in DOMAIN seq : seq[i] = e

\* Convert a sequence to the set of its elements.
SeqToSet(seq) == {seq[i] : i \in DOMAIN seq}

\* Get the last element of a sequence.
SeqLast(seq) == seq[Len(seq)]

\* Sequence empty test.
SeqEmpty(seq) == Len(seq) = 0

\* Remove all occurrences of an element from a sequence.
SeqRemove(seq, e) ==
  IF seq = <<>> THEN <<>>
  ELSE IF Head(seq) = e
       THEN SeqRemove(Tail(seq), e)
       ELSE <<Head(seq)>> \o SeqRemove(Tail(seq), e)

\* Intersection of a set of sets.
SetIntersection(ss) == {x \in UNION ss : \A t \in ss : x \in t}

\* All permutations of a finite set (as sequences of its elements).
Permutations(s) ==
  IF s = {} THEN {<<>>}
  ELSE {<<x>> \o p : x \in s, p \in Permutations(s \ {x})}

\* Test helper: writes an informative failure message without terminating.
\* It is used by other specs' assertions, not by this module itself.
\* Since this module has no actions, the message simply records the value.
TestHelper(condition, val) ==
  IF condition THEN TRUE
  ELSE LET _ == Print("TestHelper failed on value: " ^ IF val = NONE THEN "NONE" ELSE val)
       IN TRUE

\* SPECIFICATION (empty, because this module has no actors or actions).
SPECIFICATION == TRUE

\* INIT: the empty initial state, required only so the .cfg finds it.
INIT == TRUE

\* NEXT: no actions, so the spec is stutter-closed.
NEXT == UNCHANGED {}

\* INVARIANT: there is none, but the placeholder name is required by the .cfg.
INVARIANTS == TRUE

\* PROPERTY: there is none, but the placeholder name is required by the .cfg.
PROPERTIES == TRUE

====