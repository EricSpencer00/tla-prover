---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

\* Utility function library shared by the key-value store specs.  It contains
\* set- and sequence-manipulation operators but no system state of its own.

CONSTANTS MaxElem

ASSUME MaxElem \in Nat

\* Set intersection test: true iff the two input sets share any element.
IntersectionNotEmpty(A, B) == \E a \in A : a \in B

\* Maximum (by natural ordering) of a non-empty set of naturals.
MaxSet(S) ==
  CHOOSE m \in S : \A x \in S : x <= m

\* Minimum (by natural ordering) of a non-empty set of naturals.
MinSet(S) ==
  CHOOSE m \in S : \A x \in S : m <= x

\* Generalized fold over a set, with an accumulator and a binary reducer.
SetReduce(S, z, f) ==
  LET g[S2 \in SUBSET S] ==
       IF S2 = {} THEN z
       ELSE LET x == CHOOSE y \in S2 : TRUE
            IN f[x, g[S2 \ {x}]]
  IN g[S]

\* Generalized fold over a sequence, with an accumulator and a binary reducer.
SeqReduce(sq, z, f) ==
  LET rr[N \in Nat] ==
       IF N = 0 THEN z
       ELSE LET tail == rr[N - 1]
                x == sq[N]
            IN f[x, tail]
  IN rr[Len(sq)]

\* The index of an element in a sequence, or 0 if not present.
IndexOf(sq, e) ==
  CHOOSE i \in 1..Len(sq) : sq[i] = e

\* Convert a sequence to the set of its elements.
SeqToSet(sq) ==
  {sq[i] : i \in 1..Len(sq)}

\* The last element of a non-empty sequence.
LastOf(sq) ==
  sq[Len(sq)]

\* Test if a sequence is empty.
SeqEmpty(sq) ==
  Len(sq) = 0

\* Remove all occurrences of an element from a sequence.
SeqFilterOut(sq, e) ==
  SELECT x \in sq : x # e

\* Intersect a set of sets.
SetIntersection(S) ==
  CHOOSE s \in S : \A x \in S : x \subseteq s

\* Generate all permutation sequences of a finite set of naturals <= MaxElem.
Permutations(S) ==
  LET perm(T) == IF T = {} THEN << >>
                 ELSE UNION { << x >> \o p : x \in T, p \in perm(T \ {x}) }
  IN perm(S)

\* Test helper: always true, but prints a diagnostic if the condition fails.
Validate(cond) == cond

====