---- MODULE Quicksort ----
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen

\* A permutation of a domain: a bijection on 1..n under which the sequence
\* is composed.
PermutationOf(n) == { f \in [1..n -> 1..n] : \A a, b \in 1..n : f[a] = f[b] => a = b }

\* Sorts a (finite) sequence into non-decreasing order.
SortUpTo(n, s) ==
  [ i \in 1..n |-> CHOOSE x \in { y \in 1..n :
                  \A j \in 1..n : y[j] = s[PermutationOf(n)[j]] : \A a, b \in 1..n : a < b => y[a] <= y[b] } : TRUE ]

\* A swap-only partition: the interval's elements are only reordered, never changed,
\* and order is where the pivot cut lands rather than an absolute value check.
SwapPartition(n, s, lo, hi, p) ==
  { y \in { x \in 1..n :
      \A i \in 1..n : (i < lo \/ i > hi) => x[i] = s[i] :
      \A a, b \in lo..hi : a <= p /\ b > p => x[a] <= x[b] } : TRUE }

VARIABLES seq, origSeq, work, pc

vars == <<seq, origSeq, work, pc>>

Interval == [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]

TypeOK ==
  /\ seq \in Seq(Values)
  /\ origSeq \in Seq(Values)
  /\ work \subseteq Interval
  /\ pc \in {"loop", "done"}
  /\ Len(seq) <= MaxSeqLen

Init ==
  /\ seq \in { s \in Seq(Values) : Len(s) >= 1 /\ Len(s) <= MaxSeqLen }
  /\ origSeq = seq
  /\ work = {[lo |-> 1, hi |-> Len(seq)]}
  /\ pc = "loop"

Step ==
  /\ pc = "loop"
  /\ work # {}
  /\ \E interval \in work :
       /\ interval.lo = interval.hi
          => work' = work \ {interval}
       /\ interval.lo < interval.hi
          => \E p \in interval.lo..interval.hi :
               /\ seq' \in SwapPartition(MaxSeqLen, seq, interval.lo, interval.hi, p)
               /\ work' = (work \ {interval}) \cup {[lo |-> interval.lo, hi |-> p], [lo |-> p + 1, hi |-> interval.hi]}
  /\ pc' = "loop"
  /\ origSeq' = origSeq

Terminate ==
  /\ pc = "loop"
  /\ work = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, origSeq, work>>

Stutter ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == Step \/ Terminate \/ Stutter

Spec == Init /\ [][Next]_vars /\ WF_vars(Step) /\ WF_vars(Terminate)

\* PCorrect is the partial correctness claim; Inv is the structural
\* invariant the sort and partition steps both preserve.
PCorrect ==
  /\ (pc = "done" => seq = SortUpTo(Len(seq), origSeq))
  /\ (pc = "done" => \A a, b \in 1..Len(seq) : a <= b => seq[a] <= seq[b])

Inv ==
  /\ \A interval \in work : interval.lo <= interval.hi
  /\ (Len(seq) = Len(origSeq) /\ \E f \in PermutationOf(Len(seq)) : \A i \in 1..Len(seq) : seq[i] = origSeq[f[i]])
  /\ \A interval \in work : \A a, b \in interval.lo..interval.hi : a <= b => seq[a] <= seq[b]

Termination ==
  \A f \in [vars -> vars] : (Step \in f) /\ (Terminate \in f) ~> (Terminate \in f)

\* A bounded-length version of Seq, used only by the .cfg replacement for
\* the unbounded operator from Sequences.
LimitedSeq(n, S) ==
  { f \in [1..n -> S] : \A i \in 1..n : \E g \in [1..n -> S] : \A j \in 1..n : j <= i => g[j] = f[j] }

====