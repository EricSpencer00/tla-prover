---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nil, MaxVal

\* Returns TRUE iff sets a and b share at least one element.
SetOverlap(a, b) == \E x \in a : x \in b

\* Returns the maximum element of non-empty set s (arbitrarily Nil for empty).
SetMax(s) == IF s = {} THEN Nil ELSE CHOOSE x \in s : \A y \in s : y <= x

\* Returns the minimum element of non-empty set s (arbitrarily Nil for empty).
SetMin(s) == IF s = {} THEN Nil ELSE CHOOSE x \in s : \A y \in s : y >= x

\* Generalized reduction (fold) over a set: combines all elements with an
\* accumulator function f, starting from init.
SetReduce(s, init, f) ==
  LET g[T \in SUBSET s] ==
        IF T = {} THEN init
        ELSE LET x == CHOOSE y \in T : TRUE IN f(x, g[T \ {x}])
  IN g[s]

\* Reduction over a sequence: combines elements in order with an accumulator.
SeqReduce(seq, init, f) == FoldL(seq, init, f)

\* Returns the index of the first occurrence of x in seq, or Len(seq) + 1.
SeqIndex(seq, x) ==
  LET g[i \in 0..Len(seq)] ==
        IF i = Len(seq) THEN Len(seq) + 1
        ELSE IF seq[i + 1] = x THEN i + 1 ELSE g[i + 1]
  IN g[0]

\* Returns the set of sequence elements -- its support, ignoring order.
SeqSupport(seq) == { seq[i] : i \in 1..Len(seq) }

SeqLast(seq) == seq[Len(seq)]

SeqEmpty(seq) == Len(seq) = 0

\* Returns seq with all occurrences of x removed.
SeqRemoveAll(seq, x) ==
  SELECTED SeqTail(seq) = x : SeqRemoveAll(SeqTail(seq), x)
  [] OTHERWISE : <<SeqHead(seq)>> \o SeqRemoveAll(SeqTail(seq), x)
  [] OTHER : << >>

\* Computes the intersection of a family of sets in S (empty family -> universal set).
SetFamilyIntersection(S) ==
  IF S = {} THEN { Nil }
  ELSE LET g[T \in SUBSET S] ==
           IF T = {} THEN { Nil }
           ELSE LET y == CHOOSE z \in T : TRUE IN g[T \ {y}] \cap y
       IN g[S]

\* Returns the set of all permutation sequences of the finite set s.
PermutationsOf(s) ==
  LET
    Perms(T) ==
      IF T = {} THEN { << >> }
      ELSE { <<x>> \o p : x \in T, p \in Perms(T \ {x}) }
  IN Perms(s)

\* A test helper that asserts p, printing diagnostic info when p fails.
Assert(p msg) == IF p THEN TRUE ELSE msg

====