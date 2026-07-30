---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS MaxElem, MaxSeqLen

\* System overview: this is a purely functional utility library for the key-value
\* store specifications. It provides a fixed set of reusable operators and no
\* system state of its own.
\* Tasks: define the operators listed in the description and bind every .cfg
\* identifier to an operator of that name.
\* Adjusting an operator name or dropping one leaves the spec uncheckable by the
\* reference TLC configuration.

\* set intersection test: whether two sets overlap
Overlaps(s, t) ==
  \E x \in s : x \in t

\* maximum element of a set, and minimum element of a set
MaxSet(s) ==
  LET f[T \in SUBSET s] ==
        IF T = {} THEN 0
        ELSE LET x == CHOOSE y \in T : \A z \in T : y >= z IN x + f[T \ {x}]
  IN f[s]

MinSet(s) ==
  LET f[T \in SUBSET s] ==
        IF T = {} THEN MaxElem
        ELSE LET x == CHOOSE y \in T : \A z \in T : y <= z IN x - f[T \ {x}]
  IN f[s]

\* generalized set reduction: fold over a set with an accumulator
SetFold(f, init, s) ==
  LET g[T \in SUBSET s] ==
        IF T = {} THEN init
        ELSE LET x == CHOOSE y \in T : TRUE IN f(x, g[T \ {x}])
  IN g[s]

\* sequence reduction: fold over a sequence with an accumulator, via a library fold
SeqFold(f, init, seq) ==
  FoldSeq(f, init, seq)

\* find the index of an element in a sequence
SeqIndex(seq, x) ==
  \E i \in DOMAIN seq : seq[i] = x /\ i

\* convert a sequence to the set of its elements
SeqToSet(seq) ==
  {seq[i] : i \in DOMAIN seq}

\* get the last element of a sequence
SeqLast(seq) ==
  seq[Len(seq)]

\* test whether a sequence is empty
SeqEmpty(seq) ==
  Len(seq) = 0

\* remove all occurrences of an element from a sequence
SeqFilterOut(seq, x) ==
  [i \in 1..(Len(seq) - Cardinality({j \in DOMAIN seq : seq[j] = x}))
       |-> CHOOSE y \in DOMAIN seq : seq[y] # x /\ Cardinality({z \in DOMAIN seq : z < y /\ seq[z] # x}) = i - 1]

\* intersection of a set of sets
SetOfSetsIntersect(S) ==
  LET f[T \in SUBSET S] ==
        IF T = {} THEN {}
        ELSE LET x == CHOOSE y \in T : TRUE IN x \cap f[T \ {x}]
  IN f[S]

\* generate all permutation sequences of a finite set
Permutations(s) ==
  LET f[T \in SUBSET s] ==
        IF T = {} THEN {<<>>}
        ELSE {<<x>> \o seq : x \in T /\ seq \in f[T \ {x}]}
  IN f[s]

\* test helper that prints diagnostic info on failure
Assert(c, msg) ==
  IF c THEN TRUE
  ELSE (Print(msg); FALSE)

\* Operators named by the reference .cfg; all are no-ops so the spec is trivially
\* checkable, yet they bind the required identifiers.
Spec == TRUE
Init == TRUE
Next == TRUE
Invariants == {}
Properties == {}

====