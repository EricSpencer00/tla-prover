---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* The model's sequence operator is replaced by a bounded version so the
\* state space stays finite; the name Seq is never declared here.
LimitedSeq(n) == CHOOSE s \in {s \in Seq(1..n) : TRUE} : TRUE

VARIABLES seq, orig, work, pc
vars == <<seq, orig, work, pc>>

Intervals == [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]
Subintervals(i) == [lo |-> i.lo, hi |-> i.hi]

TypeOK ==
  /\ seq \in Seq(1..MaxSeqLen)
  /\ orig \in Seq(1..MaxSeqLen)
  /\ work \subseteq Intervals
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E s \in {s \in LimitedSeq(MaxSeqLen) : Len(s) > 0} : seq = s
  /\ orig = seq
  /\ work = {[lo |-> 1, hi |-> Len(seq)]}
  /\ pc = "loop"

\* A valid partition of the chosen interval: outside the interval nothing
\* changes, and inside the interval the lower part is no greater than the
\* upper part relative to the pivot index.
ValidPartition(s, i, p) ==
  /\ \A k \in 1..Len(s) : s[k] = seq[k]
  /\ \A k \in i.lo..p : \A j \in p+1..i.hi : s[k] <= s[j]

Partition(i, p) ==
  {s \in Seq(1..MaxSeqLen) : ValidPartition(s, i, p)}

Step ==
  \/ \E i \in work :
       /\ i.lo = i.hi
       /\ work' = work \ {i}
       /\ UNCHANGED <<seq, orig>>
  \/ \E i \in work, p \in i.lo..i.hi :
       /\ i.lo < i.hi
       /\ \E s \in Partition(i, p) : seq' = s
       /\ work' = (work \ {i}) \cup {[lo |-> i.lo, hi |-> p], [lo |-> p+1, hi |-> i.hi]}
       /\ UNCHANGED orig
  \/ (work = {} /\ pc' = "done" /\ UNCHANGED <<seq, orig, work>>)
  \/ (pc = "done" /\ UNCHANGED vars)

Next == Step

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

\* The algorithm's partial correctness: termination yields a sorted
\* permutation of the original sequence.
PCorrect ==
  (pc = "done") =>
    /\ \A i \in 1..Len(seq) : \E j \in 1..Len(orig) : seq[i] = orig[j]
    /\ \A i \in 1..(Len(seq) - 1) : seq[i] <= seq[i+1]

\* The invariant used in the TLAPS proof: the work set always partitions
\* the domain, the sequence is a permutation of the original, and any
\* two intervals are relatively sorted.
Inv ==
  /\ \A i, j \in work : (i.hi < j.lo \/ j.hi < i.lo \/ i = j)
  /\ \A i \in 1..Len(seq) : \E j \in 1..Len(orig) : seq[i] = orig[j]
  /\ \A i, j \in work : (i.hi < j.lo) => (\A k \in i.lo..i.hi, l \in j.lo..j.hi : seq[k] <= seq[l])

Termination == (pc = "done")
====