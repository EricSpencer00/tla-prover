---- MODULE Util ----
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS MaxVal, MaxSeq

NONE == "none"

VARIABLES spec
vars == <<spec>>

\* A placeholder specification operator; other modules import this file.
Spec == TRUE

Init == spec' = Spec

Next == UNCHANGED vars

Spec == Init /\ [][Next]_vars

TypeOK == spec \in BOOLEAN

SpecInv == spec

SpecProps == NONE

\* Utility operators that the description requires, in exactly this order.

\* (1) Set intersection test: two sets share any element.
SetOverlap(s, t) == \E x \in s : x \in t

\* (2) Identify the maximum element of a set of integers.
SetMax(s) ==
  IF s = {} THEN 0
  ELSE LET m == CHOOSE x \in s : \A y \in s : y <= x IN m

\* (2b) Identify the minimum element of a set of integers.
SetMin(s) ==
  IF s = {} THEN 0
  ELSE LET m == CHOOSE x \in s : \A y \in s : x <= y IN m

\* (3) Generalized reduction (fold) over a set.
SetReduce(f, init, s) ==
  LET g[T \in SUBSET s] ==
    IF T = {} THEN init
    ELSE \E x \in T : g[T \ {x}] = f(x, init)
  IN g[s]

\* (4) Reduction over a sequence, via the library fold operator.
SeqReduce(f, init, s) == Fold(f, init, s)

\* (5) Index of an element in a sequence (or 0 if not present).
SeqIndex(s, e) == CHOOSE k \in 1..Len(s) : s[k] = e

\* (6) Convert a sequence to the set of its elements.
SeqToSet(s) == { s[i] : i \in 1..Len(s) }

\* (7) The last element of a sequence.
SeqLast(s) == s[Len(s)]

\* (8) Test whether a sequence is empty.
SeqIsEmpty(s) == Len(s) = 0

\* (9) Remove all occurrences of an element from a sequence.
SeqRemove(s, e) == SelectSeq(s, LAMBDA x : x # e)

\* (10) Intersection of a set of sets.
SetIntersection(t) == \E x \in t : \A y \in t : x \subseteq y

\* (11) All permutations of the set {1, 2, ..., n} as sequences.
SetPermutations(n) ==
  { p \in [1..n -> 1..n] : \A i \in 1..n : \A j \in 1..n : i # j => p[i] # p[j] }

\* (12) Assertion test helper that always prints a diagnostic message.
TestHelper(f) == IF f THEN TRUE ELSE (Print("assertion failed"); FALSE)

====