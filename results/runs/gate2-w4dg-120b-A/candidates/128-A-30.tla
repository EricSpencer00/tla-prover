---- MODULE Quicksort ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen, Seq

Domain == 1 .. Len(Seq)

\* Intervals are always whole: this is what the invariant below is about.
Interval == { i \in Domain : i >= 1 /\ i <= Len(Seq) }

WorkSet == [lo : 1 .. MaxSeqLen, hi : 1 .. MaxSeqLen]
Atom == { x \in WorkSet : x.lo = x.hi }

\* A "partition" here is any permutation that keeps the outside of the
\* chosen interval fixed while putting the low side at or below the high side.
Partitions(a, lo, hi, pivot) ==
  { b \in [Domain -> Values] :
      \A i \in Domain :
        (i < lo \/ i > hi) => b[i] = a[i]
      /\ \A i \in lo .. pivot, j \in (pivot + 1) .. hi : b[i] <= b[j] }

\* Relates two sequences: the second is a rearrangement of the first, with no
\* copy of any domain element. The domain automorphism is a bijection that
\* moves every element it touches, so the two sequences are related by a pure
\* permutation of the indices.
Permutes(a, b) ==
  \E f \in [Domain -> Domain] :
    /\ \A x, y \in Domain : f[x] = f[y] => x = y
    /\ \A x \in Domain : f[x] # x
    /\ \A x \in Domain : b[x] = a[f[x]]

\* Relative sortedness of two disjoint intervals in the current sequence.
RelSorted(lo1, hi1, lo2, hi2) ==
  \A i \in lo1 .. hi1, j \in lo2 .. hi2 : Seq[i] <= Seq[j]

VARIABLES Seq, Orig, Work, pc

vars == <<Seq, Orig, Work, pc>>

TypeOK ==
  /\ Seq \in [Domain -> Values]
  /\ Orig \in [Domain -> Values]
  /\ Work \subseteq WorkSet
  /\ pc \in {"loop", "done"}

\* Every interval in the work set is whole, so partitioning never fragments.
DomainPartitions ==
  \A w \in Work : w.lo <= w.hi

Init ==
  /\ Seq = Seq
  /\ Orig = Seq
  /\ Work = { [lo |-> 1, hi |-> Len(Seq)] }
  /\ pc = "loop"

\* The partition step is nondeterministic in two ways: the pivot is chosen
\* from anywhere in the interval, and the output sequence is any partition
\* that satisfies the low/high ordering. The two subintervals replace the
\* one that was just split.
Step ==
  \/ \E w \in Work :
       /\ w.lo = w.hi
       /\ Work' = Work \ {w}
       /\ UNCHANGED <<Seq, Orig>>
       /\ UNCHANGED pc
  \/ \E w \in Work, pivot \in w.lo .. w.hi :
       /\ \E s \in Partitions(Seq, w.lo, w.hi, pivot) :
            /\ Seq' = s
            /\ Work' = (Work \ {w})
                        \cup { [lo |-> w.lo, hi |-> pivot]
                              , [lo |-> pivot + 1, hi |-> w.hi] }
       /\ UNCHANGED <<Orig, pc>>
  \/ \E w \in Work :
       /\ w.lo > Len(Seq)
       /\ Work' = Work \ {w}
       /\ UNCHANGED <<Seq, Orig, pc>>
  \/ (pc = "loop" /\ Work = {}) /\ pc' = "done" /\ UNCHANGED <<Seq, Orig, Work>>
  \/ (pc = "done") /\ UNCHANGED vars

Next == Step

\* A stuttering step is needed once the algorithm has terminated.
Stall == UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Stall)

PCorrect ==
  pc = "done" => (Seq \in Permutes(Orig) /\ \A i \in 1 .. (Len(Seq) - 1) : Seq[i] <= Seq[i + 1])

\* The full shape of the invariant: partitions are whole, the current
\* sequence is always a permutation of the original, and every two
\* disjoint work intervals are correctly ordered relative to each other.
Inv ==
  /\ DomainPartitions
  /\ Seq \in Permutes(Orig)
  /\ \A w1, w2 \in Work :
       (w1 # w2) => (w1.hi < w2.lo \/ w2.hi < w1.lo) => RelSorted(w1.lo, w1.hi, w2.lo, w2.hi)

Termination == <>(pc = "done")

====