---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* A finite version of the built-in Seq operator, used to keep the
\* search space finite for model checking.
LimitedSeq(S) == CHOOSE p \in { q \in Seq(V) : V \in {Values} : Len(q) <= MaxSeqLen } : p = S

Indices == 0 .. MaxSeqLen - 1

VARIABLES seq, origSeq, todo, pc
vars == <<seq, origSeq, todo, pc>>

\* Intervals are contiguous index ranges that partition the sequence
\* being sorted; each loop iteration picks one and partitions it further.
Intervals == [lo: 0 .. MaxSeqLen - 1, hi: 0 .. MaxSeqLen - 1]
IsSingleton(i) == i.lo = i.hi

RECURSIVE SumOf(_, _)
SumOf(S, r) ==
  IF S = {} THEN 0
  ELSE LET i == CHOOSE x \in S : TRUE IN r[i] + SumOf(S \ {i}, r)

\* A partition of the current sequence at pivot k over interval i: any
\* reordering that keeps elements outside i fixed, and every element at
\* or below the pivot index no greater than any element above it.
Partition(seq, i, k) ==
  { seq' \in {LimitedSeq(V) : V \in {Values}} :
      /\ \A j \in Indices : (j < i.lo \/ j > i.hi) => seq'[j] = seq[j]
      /\ \A p \in i.lo .. k, q \in (k + 1) .. i.hi : seq'[p] <= seq'[q] }

TypeOK ==
  /\ seq \in {LimitedSeq(V) : V \in {Values}}
  /\ origSeq \in {LimitedSeq(V) : V \in {Values}}
  /\ todo \subseteq Intervals
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E s \in {LimitedSeq(V) : V \in {Values}} : seq = s /\ origSeq = s
  /\ todo = {[lo |-> 0, hi |-> Len(seq) - 1]}
  /\ pc = "loop"

\* One loop iteration: partition an interval or remove a singleton.
Step ==
  /\ pc = "loop"
  /\ \E i \in todo :
       /\ i \in todo
       /\ todo' = IF IsSingleton(i) THEN todo \ {i}
                  ELSE LET k == (i.lo + i.hi) \div 2
                           lo1 == [lo |-> i.lo, hi |-> k]
                           hi1 == [lo |-> k + 1, hi |-> i.hi]
                       IN (todo \ {i}) \cup {lo1, hi1}
       /\ seq' = IF IsSingleton(i) THEN seq
                 ELSE CHOOSE seq' \in Partition(seq, i, (i.lo + i.hi) \div 2) : TRUE
  /\ UNCHANGED <<origSeq, pc>>

Done ==
  /\ pc = "loop"
  /\ todo = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, origSeq, todo>>

Quiesce ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == Step \/ Done \/ Quiesce

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

\* Partitioning only ever reorders the domain, so the sums must stay the
\* same; together with pairwise ordering across intervals this forces global sorting.
PCorrect ==
  /\ SumOf(Indices, seq) = SumOf(Indices, origSeq)
  /\ \A a \in todo, b \in todo :
       (a # b /\ a.hi < b.lo) => (seq[a.hi] <= seq[b.lo])

Inv == \A a \in todo, b \in todo : (a.hi < b.lo) => seq[a.hi] <= seq[b.lo]

Termination == <>(pc = "done")
====