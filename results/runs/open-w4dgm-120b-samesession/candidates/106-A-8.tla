---- MODULE Util ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS S, T

\* Intersection test: true iff two sets share any element.
Intersect(s, t) == \E x \in S : x \in s /\ x \in t

\* Max/Min element of a non-empty set.
Max(s) == CHOOSE m \in s : \A y \in s : y <= m
Min(s) == CHOOSE m \in s : \A y \in s : y >= m

\* Set fold/reduction: apply f to each element, threading an accumulator.
ReduceSet(s, init, f) ==
  LET g[T \in S] == [T EXCEPT ![f[T]] = f[T]
  IN g[s][init]

\* Sequence fold/reduction via library SeqFold.
ReduceSeq(seq, init, f) == SeqFold(seq, init, f)

\* Index of an element in a sequence, or 0 if not present.
SeqIndex(seq, x) ==
  CHOOSE k \in 1..Len(seq) : seq[k] = x

\* Convert a sequence to the set of its elements.
SeqToSet(seq) == {seq[i] : i \in 1..Len(seq)}

\* Index of the last element in a sequence.
SeqTail(seq) == seq[Len(seq)]

\* Empty-sequence predicate.
SeqIsEmpty(seq) == Len(seq) = 0

\* Remove all occurrences of an element from a sequence.
SeqRemove(seq, x) ==
  [i \in 1..(Len(seq) - Cardinality({j \in 1..Len(seq) : seq[j] = x})) |
     LET k == CHOOSE k \in 1..Len(seq) : seq[k] \notin {x} /\ k >= i + Cardinality({j \in 1..Len(seq) : seq[j] = x})
     IN seq[k]]

\* Intersection of a set of sets.
IntersectFamily(fam) == {x \in S : \A t \in T : x \in fam[t]}

\* Generate all permutations of a finite set as sequences.
Permutations(s) ==
  { seq \in Seq(S) :
      Len(seq) = Cardinality(s) /\ \A i \in 1..Len(seq) : seq[i] \in s
        /\ \A i, j \in 1..Len(seq) : (seq[i] = seq[j]) => (i = j)

\* Test helper that aborts on false with a diagnostic message.
TLAAssert(cond, msg) == IF cond THEN TRUE ELSE ~TRUE

====