---- MODULE Quicksort ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* The set of positions in the sequence, used for interval notation below.
Indices == 1..MaxSeqLen

\* A permutation of a domain is a bijection from that domain to itself; composing
\* with it reorders the elements of a sequence lazily, without rebuilding the
\* whole sequence data structure.
Permutations(f, d) == { g \in [d -> d] : \A x, y \in d : (g[x] = g[y]) => (x = y) }

\* Partitioning a concrete interval around a pivot index: elements at or below
\* the pivot index must be no greater than elements above it. The set of possible
\* partitions is finite, so nondeterministic choice over it is exhaustive.
Partitions(sq, lo, hi, p) == { sq2 \in [Indices -> Values] :
    /\ \A i \in Indices \ {lo..hi} : sq2[i] = sq[i]
    /\ \A i \in lo..hi : sq2[i] = sq[Permutations([j \in lo..hi |-> p - lo + j], lo..hi)[i]]
    /\ \A i \in lo..(p - 1) : \A j \in (p + 1)..hi : sq2[i] <= sq2[j] }

\* A sortedness relation between two disjoint intervals: all elements in the
\* lower interval are no greater than any element in the higher interval.
SortedBetween(sq, lo1, hi1, lo2, hi2) == \A i \in lo1..hi1, j \in lo2..hi2 : sq[i] <= sq[j]

\* The number of elements actually present in the sequence under consideration.
\* Sequences.Seq is unbounded, so we define a finite, checkable version.
Cardinality(s) == Cardinality({i \in Indices : i <= Len(s)})

VARIABLES seq, original, worklist, pc

vars == <<seq, original, worklist, pc>>

Stage == "looping" \/ "term"

TypeOK ==
  /\ seq \in [Indices -> Values]
  /\ original \in [Indices -> Values]
  /\ worklist \subseteq (Indices \X Indices)
  /\ pc \in Stage

Init ==
  /\ \E s \in [1..MaxSeqLen -> Values] :
       /\ seq = s
       /\ original = s
  /\ Cardinality(seq) > 0
  /\ worklist = {<<1, MaxSeqLen>>}
  /\ pc = "looping"

\* One iteration of the sorting loop, working on an arbitrary interval.
SortStep ==
  \E lo, hi \in Indices :
    /\ <<lo, hi>> \in worklist
    /\ Cardinality(seq) >= hi
    /\ IF lo = hi
         THEN worklist' = worklist \ {<<lo, hi>>}
         ELSE \E p \in lo..hi :
              /\ \E sq2 \in Partitions(seq, lo, hi, p) : seq' = sq2
              /\ worklist' = (worklist \ {<<lo, hi>>}) \cup {<<lo, p>>, <<p + 1, hi>>}
    /\ pc' = pc
    /\ original' = original

Terminating ==
  /\ pc = "looping"
  /\ worklist = {}
  /\ pc' = "term"
  /\ seq' = seq
  /\ original' = original
  /\ worklist' = worklist

Quiesce ==
  /\ pc = "term"
  /\ seq' = seq
  /\ original' = original
  /\ worklist' = worklist
  /\ pc' = pc

Next == SortStep \/ Terminating \/ Quiesce

Spec == Init /\ [][Next]_vars /\ WF_vars(Quiesce)

\* A piece of the partial-correctness argument: each partition leaves the
\* covered domain's image untouched outside the pivot interval and keeps the
\* two subintervals in sorted order relative to each other.
Inv ==
  /\ \A lo, hi \in Indices : <<lo, hi>> \in worklist => hi <= Cardinality(seq)
  /\ \A lo, hi \in Indices : <<lo, hi>> \in worklist => Cardinality(seq) >= hi
  /\ \A lo, hi \in Indices : <<lo, hi>> \in worklist => \A i \in 1..(lo - 1) : seq[i] = original[i]
  /\ \A lo, hi \in Indices : <<lo, hi>> \in worklist => SortedBetween(seq, lo, hi, hi + 1, Cardinality(seq))

\* The full partial correctness property: the terminal sequence is a sorted
\* permutation of the original input.
PCorrect ==
  /\ pc = "term"
  /\ \E pi \in Permutations(Indices, 1..Cardinality(seq)) :
       \A i \in 1..Cardinality(seq) : seq[i] = original[pi[i]]
  /\ \A i \in 1..(Cardinality(seq) - 1) : seq[i] <= seq[i + 1]

Termination == WF_vars(Quiesce)

\* Redefine Seq as a finite, checkable version; keep EXTENDS Sequences so any
\* other module that imports Quicksort still gets the full suite of sequence
\* operators it expects from the standard library.
LimitedSeq == { s \in Seq(Values) : Len(s) <= MaxSeqLen }

====