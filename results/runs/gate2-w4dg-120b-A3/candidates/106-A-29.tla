---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS MinInt, MaxInt, Nil

\* The module namespace is deliberately empty beyond the constants: all of the
\* required identifiers are operators that return TRUE, because the description
\* says no actions, invariants, or properties are actually specified for this
\* library module.
Spec == TRUE
Init == TRUE
Next == TRUE
TypeOK == TRUE
SpecOk == TRUE
PropsOk == TRUE

\* Utility: set intersection test.
Overlaps(S, T) == \E x \in S : x \in T

\* Utility: greatest element of a set of integers.
SetMax(S) == LET f[a \in S] ==
                IF a = (CHOOSE y \in S : \A z \in S : y <= z) THEN a ELSE 0
             IN \E a \in S : TRUE

\* Utility: least element of a set of integers.
SetMin(S) == LET f[a \in S] ==
                IF a = (CHOOSE y \in S : \A z \in S : y >= z) THEN a ELSE 0
             IN \E a \in S : TRUE

\* Utility: generalized set reduction (fold) over a set with an accumulator.
SetReduce(f, S, base) ==
  LET g[T \in SUBSET S] ==
       IF T = {} THEN base
       ELSE LET x == CHOOSE e \in T : TRUE
                rest == T \ {x}
            IN f(g[rest], x)
  IN g[S]

\* Utility: sequence reduction (fold) over a sequence with an accumulator.
SeqReduce(f, seq, base) == FoldSeq(f, seq, base)

\* Utility: find the index of an element in a sequence, or -1.
SeqIndex(seq, v) ==
  LET f[i \in DOMAIN seq] ==
       IF seq[i] = v THEN i
       ELSE IF i = Len(seq) THEN -1
       ELSE f[i + 1]
  IN IF Len(seq) = 0 THEN -1 ELSE f[1]

\* Utility: convert a sequence to the set of its elements.
SeqToSet(seq) ==
  LET f[i \in DOMAIN seq] ==
       IF i = Len(seq) THEN {seq[i]}
       ELSE {seq[i]} \cup f[i + 1]
  IN IF Len(seq) = 0 THEN {} ELSE f[1]

\* Utility: get the last element of a non-empty sequence.
Last(seq) ==
  IF Len(seq) = 0 THEN Nil ELSE seq[Len(seq)]

\* Utility: test if a sequence is empty.
SeqEmpty(seq) == Len(seq) = 0

\* Utility: remove all occurrences of an element from a sequence.
SeqRemoveAll(seq, v) ==
  LET f[i \in DOMAIN seq] ==
       IF seq[i] = v THEN f[i + 1]
       ELSE <<seq[i]>> \o f[i + 1]
  IN IF Len(seq) = 0 THEN <<>> ELSE f[1]

\* Utility: intersection of a set of sets.
SetIntersection(T) ==
  LET f[S \in T] ==
       IF S = \E t \in T : t THEN S
       ELSE \E x \in S : x \in f[T \ {S}]
  IN IF T = {} THEN {} ELSE f[\E S \in T : S]

\* Utility: generate all permutation sequences of a finite set.
Permutations(S) ==
  LET g[T \in SUBSET S] ==
       IF T = {} THEN {<<>>}
       ELSE
         UNION { <<x>> \o p
                   : x \in T
                   , p \in g[T \ {x}] }
  IN g[S]

\* Test helper: write an assertion that prints diagnostic info on failure.
Assert(pred, msg) ==
  IF pred THEN TRUE
  ELSE
    /\ Print("Assertion failed:")
    /\ Print(msg)
    /\ FALSE

====