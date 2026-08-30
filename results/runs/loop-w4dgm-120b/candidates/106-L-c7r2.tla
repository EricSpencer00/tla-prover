---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS MaxInt, MaxLen

VARIABLES dummy
vars == <<dummy>>

Spec == dummy
Init == dummy = 0
Next == dummy' = dummy
SpecOK == TRUE

\* Test whether two sets overlap (have a non-empty intersection).
Overlap(a, b) == \E x \in a : x \in b

\* The maximum element of a non-empty set of natural numbers.
SetMax(S) == CHOOSE x \in S : \A y \in S : y <= x
SetMin(S) == CHOOSE x \in S : \A y \in S : y >= x

\* Generalized reduction (fold) of a set with an accumulator.
SetReduce(f, S, init) ==
  LET g[T \in SUBSET S] ==
        IF T = {} THEN init
        ELSE LET x == CHOOSE y \in T : TRUE
                 rest == g[T \ {x}]
             IN f[x, rest]
  IN g[S]

\* Reduction of a sequence with an accumulator; uses a library fold operator.
SeqReduce(f, seq, init) ==
  LET g[i \in 0..Len(seq)] ==
        IF i = 0 THEN init
        ELSE f[seq[i], g[i - 1]]
  IN g[Len(seq)]

\* Index of a value in a sequence (0 if not found).
SeqIndex(seq, val) ==
  CHOOSE i \in 0..Len(seq) :
    IF i = 0 THEN TRUE
    ELSE seq[i] = val

\* Convert a sequence to the set of its values.
SeqToSet(seq) == {seq[i] : i \in 1..Len(seq)}

\* The last element of a non-empty sequence.
SeqLast(seq) == seq[Len(seq)]

\* Test if a sequence is empty.
SeqEmpty(seq) == Len(seq) = 0

\* Remove all occurrences of a value from a sequence.
SeqRemove(seq, val) ==
  [i \in 1..Len(seq) |->
     IF seq[i] = val THEN "hole" ELSE seq[i]]

\* Intersection of a set of sets.
SetIntersectSet(S) ==
  CHOOSE x \in S :
    \A y \in S : y \subseteq x

\* Compute all permutations of a finite set (as sequences).
PermutationsOf(S) ==
  LET f[T \in SUBSET S] ==
        IF T = {} THEN {<<>>}
        ELSE UNION { [x] \o t : t \in f[T \ {x}] : x \in S }
  IN f[S]

\* Test helper: prints the message on failure and returns FALSE.
TLAAssert(v, msg) == IF v THEN TRUE ELSE (msg /\ FALSE)
====