---- MODULE Quicksort ----
EXTENDS Naturals, Sequences

CONSTANTS Values, MaxSeqLen

\* Sort a sequence by recursively partitioning index intervals; partition
\* results are nondeterministic but must preserve domain content and ordering.
SeqDom == 1..MaxSeqLen

VARIABLES seq, orig, pending, pc

vars == <<seq, orig, pending, pc>>

Intervals == [lo: SeqDom, hi: SeqDom]

TypeOK ==
  /\ seq \in [SeqDom -> Values]
  /\ orig \in [SeqDom -> Values]
  /\ pending \subseteq Intervals
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E s \in [SeqDom -> Values] : seq = s
  /\ orig = seq
  /\ pending = {[lo |-> 1, hi |-> MaxSeqLen]}
  /\ pc = "loop"

\* Domain partition: each interval is either untouched or split around a pivot.
DomainSplit ==
  /\ \A a, b \in pending : (a.lo <= b.lo /\ b.lo <= a.hi) => a = b
  /\ \A x \in SeqDom :
       \/ \E a \in pending : x \in a.lo..a.hi
       \/ \A a \in pending : x < a.lo \/ x > a.hi

Permutations ==
  \E g \in [SeqDom -> SeqDom] :
    /\ \A x \in SeqDom : g[x] \in SeqDom
    /\ \A x \in SeqDom : g[x] = x \/ \E y \in SeqDom : g[x] = y /\ g[y] = x
    /\ \A x \in SeqDom : seq[x] = orig[g[x]]

RelSorted ==
  \A x, y \in SeqDom : (x < y) => (seq[x] <= seq[y])

Inv == DomainSplit /\ Permutations /\ RelSorted

Partition(seq, seg, k) ==
  { t \in [SeqDom -> Values] :
      /\ \A x \in SeqDom : (x < seg.lo \/ x > seg.hi) => t[x] = seq[x]
      /\ \A x \in seg.lo..k : \A y \in (k+1)..seg.hi : t[x] <= t[y] }

SortStep ==
  /\ pc = "loop"
  /\ pending # {}
  /\ \E seg \in pending :
       /\ pending' = pending \ {seg}
       /\ IF seg.lo = seg.hi
            THEN UNCHANGED <<seq, pending>>
            ELSE
              /\ \E k \in seg.lo..seg.hi :
                   /\ \E t \in Partition(seq, seg, k) : seq' = t
                   /\ pending' = pending \cup {[lo |-> seg.lo, hi |-> k], [lo |-> k+1, hi |-> seg.hi]}
  /\ pc' = pc

Done ==
  /\ pc = "loop"
  /\ pending = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, orig, pending>>

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == SortStep \/ Done \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

PCorrect == (pc = "done") => (Permutations /\ RelSorted)

Termination == (pc = "loop") ~> (pc = "done")

LimitedSeq == Seq

====