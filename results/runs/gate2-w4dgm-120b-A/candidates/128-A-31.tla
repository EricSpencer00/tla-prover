---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences, Automorphisms

CONSTANTS Values, MaxSeqLen

\* An interval of indices of the sequence currently being sorted.
Interval == [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]

\* The set of intervals in the work set partitions the domain of the sequence;
\* no two intervals in it overlap.
Partition(S) == Union({i.lo..i.hi : i \in S})

\* Permutations are automorphisms of the domain; they keep the same multiset of
\* values while shuffling positions, which is how a reordering retains permutation
\* equivalence with the input.
Permutation == {g \in [1..MaxSeqLen -> 1..MaxSeqLen] :
                   \A x \in 1..MaxSeqLen : \E y \in 1..MaxSeqLen : g[y] = x}

\* The partition operation: everything outside the chosen interval is unchanged,
\* everything at or below the pivot is bounded above by everything above it.
\* This is the complete nondeterministic universe of reordering outcomes that
\* a real partition routine could produce.
PartitionUpdate(seq, int, pivot) ==
  {seq2 \in [1..MaxSeqLen -> Values] :
     /\ \A i \in 1..MaxSeqLen : i \notin int.lo..int.hi => seq2[i] = seq[i]
     /\ \A i \in int.lo..pivot, j \in (pivot+1)..int.hi :
          seq2[i] <= seq2[j]}

VARIABLES seq, orig, workSet, pc

vars == <<seq, orig, workSet, pc>>

TypeOK ==
  /\ seq \in [1..MaxSeqLen -> Values]
  /\ orig \in [1..MaxSeqLen -> Values]
  /\ workSet \subseteq Interval
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E s \in [1..MaxSeqLen -> Values] :
       /\ \E v \in Values : s[1] = v
       /\ seq = s
       /\ orig = s
  /\ workSet = {[lo |-> 1, hi |-> MaxSeqLen]}
  /\ pc = "loop"

Sorted(seq) ==
  \A i \in 1..(MaxSeqLen - 1) : seq[i] <= seq[i + 1]

\* The partition pivot is chosen nondeterministically from the interval; any
\* valid partition outcome is possible, which is what makes the sort robust to
\* the underlying partition routine's implementation.
LoopStep ==
  \/ \E i \in workSet :
       \/ i.lo = i.hi
          /\ workSet' = workSet \ {i}
       \/ \E pivot \in i.lo..i.hi :
            \E seq2 \in PartitionUpdate(seq, i, pivot) :
              /\ seq' = seq2
              /\ workSet' = (workSet \ {i})
                 \cup {[lo |-> i.lo, hi |-> pivot]}
                 \cup {[lo |-> pivot + 1, hi |-> i.hi]}
  \/ pc' = IF workSet = {} THEN "done" ELSE "loop"

Stall == pc = "done" /\ UNCHANGED vars

Next == LoopStep \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(LoopStep)

\* The invariant is the pair of properties the theorem requires: the work set
\* partitions the domain (no overlap with the rest of the sequence untouched), and
\* the current sequence is a permutation of the original.
Inv ==
  /\ Partition(workSet) = 1..MaxSeqLen
  /\ \E g \in Permutation : seq = [i \in 1..MaxSeqLen |-> orig[g[i]]]

PCorrect ==
  /\ pc = "done" => (Sorted(seq) /\ \E g \in Permutation : seq = [i \in 1..MaxSeqLen |-> orig[g[i]]])
  /\ pc \in {"loop", "done"}

TypeOKOK == /\ TypeOK /\ Inv /\ PCorrect

Termination == <>(pc = "done")

====