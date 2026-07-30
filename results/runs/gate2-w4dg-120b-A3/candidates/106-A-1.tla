---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS MaxSeqLen, MaxSetSize

\* Helper for printing values, used by the Test helper operator below
Print(v) == v

\* (1) Set intersection test: whether two sets overlap
Intersect(s, t) == \E x \in s : x \in t

\* (2) Maximum element of a set
MaxSet(s) == LET g[T \in SUBSET s] ==
                  IF T = {} THEN 0
                  ELSE LET x \in T == CHOOSE x \in T : \A y \in T : y <= x
                       IN x
              IN g[s]

\* (2) Minimum element of a set
MinSet(s) == LET g[T \in SUBSET s] ==
                  IF T = {} THEN 0
                  ELSE LET x \in T == CHOOSE x \in T : \A y \in T : y >= x
                       IN x
              IN g[s]

\* (3) Generalized set reduction (fold) with an accumulator
SetReduce(f, s, init) ==
  LET g[T \in SUBSET s] ==
        IF T = {} THEN init
        ELSE LET x \in T == CHOOSE x \in T : TRUE
                 rest == g[T \ {x}]
             IN f(x, rest)
  IN g[s]

\* (4) Sequence reduction (fold) using the library operator
SeqReduce(f, seq, init) == Reduce(f, seq, init)

\* (5) Index of an element in a sequence, or 0 if absent
SeqIndex(seq, e) ==
  LET g[i \in 0..Len(seq)] ==
        IF i = Len(seq) THEN 0
        ELSE IF seq[i + 1] = e THEN 1 + i
        ELSE g[1 + i]
  IN g[0]

\* (6) Convert a sequence to the set of its elements
SeqToSet(seq) == {seq[i] : i \in 1..Len(seq)}

\* (7) The last element of a non-empty sequence
Last(seq) == seq[Len(seq)]

\* (8) Test if a sequence is empty
IsEmpty(seq) == Len(seq) = 0

\* (9) Remove all occurrences of an element from a sequence
RemoveAll(seq, e) ==
  IF seq = <<>> THEN <<>>
  ELSE IF Head(seq) = e THEN RemoveAll(Tail(seq), e)
  ELSE <<Head(seq)>> \o RemoveAll(Tail(seq), e)

\* (10) Intersection of a set of sets
SetIntersection(ss) == {x \in UNION ss : \A s \in ss : x \in s}

\* (11) Generate all permutation sequences of a finite set
Permutations(s) ==
  LET g[T \in SUBSET s] ==
        IF T = {} THEN {<<>>}
        ELSE LET seqs == {<<x>> \o p : x \in T, p \in g[T \ {x}]}
             IN seqs
  IN g[s]

\* (12) A test helper: evaluates a test expression and prints diagnostics on failure
Test(name, expr) ==
  IF expr THEN TRUE
  ELSE Print(name) /\ Print("FAILED") /\ FALSE

\* No actors or system components: this module is a purely functional library of
\* reusable operators, and the spec below is the degenerate specification for a
\* specification that has no actors and no state.
Spec == TRUE

Init == TRUE
Next == UNCHANGED Spec
INVARIANT TypeOK == Spec
PROPERTY LivenessOK == Spec

====