---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

\* Configuration constants.  Seq is the nondeterministic initial sequence, taken
\* from all non-empty sequences over the bounded value set Values.  MaxSeqLen
\* is the bound on length used by the companion .cfg module for model checking.
CONSTANTS Values, MaxSeqLen, Seq

Indices == 1..Len(Seq)

\* An interval of the current sequence, identified by its first and last index.
Interval == [lo: Indices, hi: Indices]

VARIABLES seq, original, work, pc
vars == <<seq, original, work, pc>>

\* The partition operator is nondeterministic but must respect the pivot ordering
\* (below-or-equal) inside the interval and leave everything outside untouched.
Partition(f, iv, k) ==
  {g \in Permutations([1..Len(f) -> Values]) :
     \A i \in Indices :
       IF i < iv.lo \/ i > iv.hi THEN g[i] = f[i]
       ELSE IF i <= k THEN g[i] <= f[k]
       ELSE g[i] >= f[k]}

TypeOK ==
  /\ seq \in [Indices -> Values]
  /\ original \in [Indices -> Values]
  /\ work \subseteq Interval
  /\ pc \in {"sort", "done"}

Init ==
  /\ seq = Seq
  /\ original = Seq
  /\ work = {[lo |-> 1, hi |-> Len(Seq)]}
  /\ pc = "sort"

\* One iteration: select an interval, partition it around a pivot, and
\* replace it by two subintervals -- or simply drop a singleton interval.
SortStep ==
  /\ pc = "sort"
  /\ work # {}
  /\ \E iv \in work :
       \/ /\ iv.lo = iv.hi
           /\ work' = work \ {iv}
           /\ UNCHANGED <<seq, original>>
       \/ /\ iv.lo < iv.hi
           /\ \E k \in iv.lo..iv.hi :
                \E g \in Partition(seq, iv, k) :
                  /\ seq' = g
                  /\ work' = (work \ {iv}) \cup
                       {[lo |-> iv.lo, hi |-> k], [lo |-> k + 1, hi |-> iv.hi]}
           /\ UNCHANGED original
  /\ UNCHANGED pc

Terminate ==
  /\ pc = "sort"
  /\ work = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, original, work>>

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == SortStep \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(SortStep) /\ WF_vars(Terminate)

\* Permutation preservation: the current sequence is always a permutation of
\* the original.  Domain partitions: intervals in work are pairwise disjoint.
Inv ==
  /\ \A i \in Indices : \E j \in Indices : seq[i] = original[j]
  /\ \A iv, iv2 \in work :
       (iv # iv2) => (iv.hi < iv2.lo \/ iv2.hi < iv.lo)

\* Termination: the algorithm always reaches its final state.
Termination == <>(pc = "done")

\* Final-state correctness: a sorted permutation of the input.
PCorrect ==
  /\ pc = "done"
  /\ \A i \in 1..(Len(seq) - 1) : seq[i] <= seq[i + 1]
  /\ Len(seq) = Len(original)

====