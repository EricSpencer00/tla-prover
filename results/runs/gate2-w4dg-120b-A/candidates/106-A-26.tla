---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS MaxVal, Nil, EmptySeq
ASSUME Nil \notin (0..MaxVal) /\ EmptySeq \in Seq((0..MaxVal) \cup {Nil})

\* Intersection test: true iff the two sets have a common element.
Intersects(S, T) == \E x \in S : x \in T

\* Maximum element in a non-empty set.
MaxSet(S) == CHOOSE x \in S : \A y \in S : y <= x
\* Minimum element in a non-empty set.
MinSet(S) == CHOOSE x \in S : \A y \in S : y >= x

\* Generalized set reduction (fold): combines elements of S into an
\* accumulator acc using the binary operator \oplus (commutative, assoc).
SetReduce(S, \oplus, acc) ==
  LET elems == CHOOSE e \in (SUBSET S) : TRUE
      fold[T \in SUBSET elems] ==
        IF T = {} THEN acc
        ELSE LET x == CHOOSE y \in T : TRUE IN \oplus[x, fold[T \ {x}]]
  IN fold[elems]

\* Sequence reduction (fold) using the library's SeqReduce.
SeqReduceSeq(seq, \oplus, acc) == SeqReduce(seq, \oplus, acc)

\* Find the index of element x in sequence s; Nil if not present.
SeqIndex(s, x) ==
  LET idx[i \in 0..Len(s)] ==
        IF i = Len(s) THEN Nil
        ELSE IF s[i + 1] = x THEN i + 1
        ELSE idx[i + 1]
  IN idx[0]

\* Convert a sequence to the set of its elements.
SeqToSet(s) == { s[i] : i \in 1..Len(s) }

\* The last element of a non-empty sequence.
LastOf(s) == s[Len(s)]

\* True when the sequence is empty.
IsEmpty(s) == Len(s) = 0

\* Remove all occurrences of x from sequence s.
SeqRemove(s, x) ==
  [i \in 1..(Len(s) - Cardinality({k \in 1..Len(s) : s[k] = x})) |
     IF \E j \in 1..Len(s) : s[j] # x /\ \A k \in 1..Len(s) : (s[k] = s[j] => k <= j) /\ j = i
     THEN s[j] ELSE Nil]

\* Intersection of a set of sets.
SetIntersection(G) ==
  IF G = {} THEN {}
  ELSE LET x \in G IN CHOOSE y \in G : \A z \in G : y \subseteq z

\* Generate all permutation sequences of a finite set S.
Permutations(S) ==
  IF S = {} THEN {EmptySeq}
  ELSE { <<x>> \o p \in Permutations(S \ {x}) : x \in S }

\* Test helper: prints diagnostic info on a failed assertion.
Assert(cond, msg) ==
  IF cond THEN TRUE
  ELSE LET _ == msg IN FALSE

SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====