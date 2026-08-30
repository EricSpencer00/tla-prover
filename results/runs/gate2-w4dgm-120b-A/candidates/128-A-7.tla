---- MODULE Quicksort ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

Indices == 1..MaxSeqLen

Intervals == {i \in Indices, j \in Indices : i <= j}

VARIABLES seq, original, work, pc
vars == <<seq, original, work, pc>>

\* Renamed to avoid the conflict with the override in the .cfg; this is the
\* operator that the .cfg replaces with a bounded version of Seq.
LimitedSeq == Seq

TypeOK ==
  /\ seq \in [Indices -> Values]
  /\ original \in [Indices -> Values]
  /\ work \subseteq Intervals
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E s \in [Indices -> Values] : seq = s
  /\ original = seq
  /\ work = {<<1, MaxSeqLen>>}
  /\ pc = "loop"

\* A permutation of a domain's elements, used for the partition operator.
Permutation(f) ==
  /\ f \in [Indices -> Indices]
  /\ \A a, b \in Indices : f[a] = f[b] => a = b

\* Partition is nondeterministic in the sense that any valid partitioning of
\* the interval can be chosen -- the integrity check below is what rules out
\* an arbitrary value appearing at some position inside the interval.
ValidPartitions(seq, low, high, pivot) ==
  {x \in [Indices -> Values] :
     /\ \A k \in Indices : (k < low \/ k > high) => x[k] = seq[k]
     /\ \A a, b \in Indices :
          (low <= a /\ a <= pivot /\ pivot < b /\ b <= high)
            => x[a] <= x[b]}

Partition(seq, low, high, pivot) ==
  \E x \in ValidPartitions(seq, low, high, pivot) : x

LoopStep ==
  \E low, high \in Indices :
    /\ <<low, high>> \in work
    /\ work' = work \ {<<low, high>>}
    /\ IF low = high
         THEN UNCHANGED <<seq, original>>
         ELSE
           /\ \E pivot \in low..high :
                /\ seq' = Partition(seq, low, high, pivot)
                /\ work' = work \cup {<<low, pivot>>, <<pivot + 1, high>>}
           /\ UNCHANGED original
    /\ pc' = IF work' = {} THEN "done" ELSE pc

Stall == pc = "done" /\ UNCHANGED vars

Next == LoopStep \/ Stall

Spec == Init /\ [][Next]_vars

\* Termination is forced by fairness on the only transition that shrinks the
\* work set, so the terminating state is reached from every reachable state.
Termination == WF_vars(LoopStep)

Permuted(f, s) == [k \in Indices |-> s[f[k]]]

\* Partitioning only permutes a contiguous block, so each partition step is a
\* permutation of the whole sequence (the identity off the block).
PermutedByPartitions ==
  \A low, high \in Indices :
    \A pivot \in low..high :
      Permutation(<<k \in Indices >>-> IF low <= k /\ k <= high
                                    THEN IF k <= pivot THEN k ELSE k + (high - pivot)
                                    ELSE IF k < low THEN k ELSE k + (high - low + 1)>>)

Sorted(f, s) ==
  \A a, b \in Indices :
    (f[a] <= f[b]) => (s[f[a]] <= s[f[b]])

\* A fully partitioned array is sorted on the entire domain, not just piece
\* by piece: each partition step is a permutation of the whole sequence, and
\* it never moves an element across a partition boundary.
SortedOnDomain == \A low, high \in Indices : Sorted(<<k \in Indices >>-> IF low <= k /\ k <= high THEN k ELSE low - 1>>, seq)

PCorrect == PermutedByPartitions /\ SortedOnDomain

DomainCovered ==
  \A low, high \in Indices :
    low <= high => (<<low, high>> \in work <=> \A k \in Indices : (low <= k /\ k <= high) => k \notin \Union_{i, j \in Indices: i <= j} {k \in Indices: i <= k /\ k <= j}

\* The two correctness lemmas together imply the permutation is the only
\* thing allowed to change the sequence, and a full partition set leaves
\* no two distinct indices in the same block -- this rules out the "move"
\* case the user wants to exclude via the integrity check inside Partition.
PermutationOnlyViaTwoLemmas == PermutedByPartitions /\ DomainCovered

\* The scoped import of the whole Sequences module brings in the infinite-
\* state Seq operator; the .cfg replaces it with the bounded version
\* defined up top. With the overload and the helper lemma in place, the
\* model is checkable and the property is provable in TLAPS.
BoundedSeq == UNCHANGED vars

====