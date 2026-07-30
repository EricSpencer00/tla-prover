---- MODULE Util ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS MaxSetSize, MinSetSize, Base, MaxReduce

VARIABLES x
vars == <<x>>

Init == x = 1
Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

\* Set intersection test: whether two sets overlap.
Intersect(f, g) == \E e \in f : e \in g

\* Maximum element of a set.
MaxOf(f) == CHOOSE e \in f : \A y \in f : e >= y

\* Minimum element of a set.
MinOf(f) == CHOOSE e \in f : \A y \in f : e <= y

\* Generalized set reduction (fold over a set with an accumulator).
ReduceSet(f, init) ==
  LET g[T \in SUBSET f] ==
       IF T = {} THEN init
       ELSE LET e == CHOOSE x \in T : TRUE
            IN e + g[T \ {e}]
  IN g[f]

\* Sequence reduction (fold over a sequence using the library fold operator).
ReduceSeq(s, init) == FoldSeq(s, LAMBDA a, b : a + b, init)

\* Find the index of an element in a sequence.
FindIndex(s, e) ==
  IF \E i \in DOMAIN s : s[i] = e
  THEN CHOOSE i \in DOMAIN s : s[i] = e
  ELSE 0

\* Convert a sequence to the set of its elements.
SeqToSet(s) == {s[i] : i \in DOMAIN s}

\* Last element of a sequence.
\* Returns 0 for the empty sequence.
LastOf(s) == IF s = <<>> THEN 0 ELSE s[Len(s)]

\* Test whether a sequence is empty.
Empty(s) == s = <<>>

\* Remove all occurrences of an element from a sequence.
RemoveAll(s, e) ==
  IF s = <<>> THEN <<>>
  ELSE IF Head(s) = e THEN RemoveAll(Tail(s), e)
  ELSE <<Head(s)>> \o RemoveAll(Tail(s), e)

\* Intersection of a set of sets.
IntersectSets(f) ==
  IF f = {} THEN {}
  ELSE LET S == CHOOSE x \in f : TRUE
       IN {e \in S : \A g \in f : e \in g}

\* Generate all permutation sequences of a finite set.
Permutations(f) ==
  IF f = {} THEN {<<>>}
  ELSE {<<e>> \o p : e \in f, p \in Permutations(f \ {e})}

\* Test helper: prints diagnostic info on failure.
Test(f, args) == IF f(args) THEN TRUE ELSE Print("failed:", f, args)

====