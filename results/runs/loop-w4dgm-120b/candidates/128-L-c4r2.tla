---- MODULE Quicksort ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* A finite, checkable version of Seq, overriding the full Seq from Sequences.
LimitedSeq(f) == {<<i, f[i]>> : i \in DOMAIN f}

VARIABLES seq, original, work, pc

vars == <<seq, original, work, pc>>

Intervals == {[lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]}

TypeOK ==
  /\ seq \in [1..MaxSeqLen -> Values]
  /\ original \in [1..MaxSeqLen -> Values]
  /\ work \in SUBSET Intervals
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E s \in [1..MaxSeqLen -> Values] :
       /\ seq = s
       /\ original = s
  /\ work = {[lo |-> 1, hi |-> MaxSeqLen]}
  /\ pc = "loop"

Partitioned(i, lo, hi) ==
  /\ \A k \in lo..hi : i[k] <= i[hi]
  /\ \A k \in 1..(lo - 1) : i[k] = seq[k]
  /\ \A k \in (hi + 1)..MaxSeqLen : i[k] = seq[k]

\* One iteration: partition an interval into two around a pivot, with the
\* result chosen nondeterministically from all valid partition outcomes.
SortStep ==
  \/ pc = "loop" /\ work # {}
       /\ \E iv \in work :
            \/ /\ iv.lo = iv.hi
               /\ work' = work \ {iv}
            \/ /\ iv.lo < iv.hi
               /\ \E p \in iv.lo..iv.hi :
                    /\ \E i \in [1..MaxSeqLen -> Values] :
                         /\ Partitioned(i, iv.lo, iv.hi)
                         /\ seq' = i
                    /\ work' = (work \ {iv}) \cup {[lo |-> iv.lo, hi |-> p],
                                                  [lo |-> p + 1, hi |-> iv.hi]}
  /\ original' = original
  /\ pc' = "loop"

Terminate ==
  /\ pc = "loop" /\ work = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, original, work>>

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == SortStep \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars
            /\ WF_vars(SortStep)
            /\ WF_vars(Terminate)

Permutation(f, g) ==
  \E h \in {[1..MaxSeqLen -> 1..MaxSeqLen] |
               \A x \in 1..MaxSeqLen : \E y \in 1..MaxSeqLen : h[x] = y} :
        \A x \in 1..MaxSeqLen : g[x] = f[h[x]]

\* Intervals on the left and on the right of a partition are sorted internally.
SortedIntervals ==
  \A iv \in Intervals :
    (iv \in work /\ iv.lo < iv.hi) => (\A j \in iv.lo..(iv.hi - 1) : seq[j] <= seq[j + 1])

PCorrect == pc = "done" => Permutation(seq, original)
TypeOK == TypeOK
Inv == Permutation(seq, original) /\ SortedIntervals

Termination == pc = "done"

====