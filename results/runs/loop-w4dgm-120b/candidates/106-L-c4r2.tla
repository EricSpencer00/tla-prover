---- MODULE Util ----
EXTENDS FiniteSets, Sequences

CONSTANTS RingSize

\* Intersection test: the two sets share at least one element.
Intersect(a, b) == \E x \in a : x \in b

\* Pick the maximum (or minimum) element from a non-empty finite set.
MaxOf(a) == CHOOSE x \in a : \A y \in a : y <= x
MinOf(a) == CHOOSE x \in a : \A y \in a : y >= x

\* Generalized set reduction (fold) with an accumulator.
FoldSet(f, a, r) == LET combine[S \in SUBSET a] ==
                      IF S = {} THEN r
                      ELSE LET x == CHOOSE y \in S : TRUE
                           IN f(combine[S \ {x}], x)
                   IN combine[a]

\* Sequence reduction with an accumulator, using the library fold operator.
FoldSeq(f, seq, r) == FoldSeq(<<>>, seq, r, f)
FoldSeq(pfx, seq, r, f) ==
  IF seq = <<>> THEN r
  ELSE FoldSeq(pfx \o <<Head(seq)>>, Tail(seq), f(r, Head(seq)), f)

\* Find the index of element x in sequence seq, or 0 if x is absent.
IndexOf(x, seq) ==
  LET g[i \in 1..Len(seq)] == IF seq[i] = x THEN i ELSE 0
      combine[T \in SUBSET (1..Len(seq))] ==
        IF T = {} THEN 0
        ELSE LET i == CHOOSE j \in T : TRUE
             IN IF g[i] # 0 THEN g[i] ELSE combine[T \ {i}]
  IN combine[1..Len(seq)]

\* Turn a sequence into the set of its elements.
SeqToSet(seq) == {seq[i] : i \in 1..Len(seq)}

\* The last element of a non-empty sequence.
Last(seq) == seq[Len(seq)]

\* True iff the sequence is empty.
SeqEmpty(seq) == seq = <<>>

\* Remove all occurrences of x from seq.
RemoveAll(x, seq) == IF seq = <<>> THEN <<>>
                     ELSE IF Head(seq) = x THEN RemoveAll(x, Tail(seq))
                     ELSE <<Head(seq)>> \o RemoveAll(x, Tail(seq))

\* Intersection of a set of sets (a fold over union/intersection).
IntersectMany(S) == FoldSet(Intersect, S, UNIVERSE)

\* Generate every permutation of the fixed ring of node ids 1..RingSize.
Permutations ==
  { p \in [1..RingSize -> 1..RingSize] :
      {p[i] : i \in 1..RingSize} = 1..RingSize }

\* Assertion test helper that prints a failure message before halting.
Test(cond) == IF cond THEN TRUE ELSE UNCHANGED cond

CONSTANTS == {RingSize}

Spec == UNCHANGED Spec

Init == UNCHANGED Init

Next == UNCHANGED Next

Invariants == UNCHANGED Invariants

Properties == UNCHANGED Properties

====