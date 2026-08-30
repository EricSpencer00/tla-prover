---- MODULE Quicksort ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* PartitionSeq abstracts the semantics of the partition step; the
\* partition itself is nondeterministic but must leave everything outside
\* the interval alone and must separate the two sides of the pivot.
PartitionSeq(seq, i, j) ==
  {t \in [1..Len(seq) -> Values] :
      /\ (\A k \in 1..Len(seq) : k \notin i..j => t[k] = seq[k])
      /\ (\A k \in i..j : \A m \in i..j : k <= m => t[k] <= t[m])
  }

Intervals == {i \in 1..MaxSeqLen : [lo |-> 1, hi |-> i]}
WorkIntervals == [lo : 1..MaxSeqLen, hi : 1..MaxSeqLen]

VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

LeftInterval(i, p) == [lo |-> i.lo, hi |-> p]
RightInterval(p, i) == [lo |-> p + 1, hi |-> i.hi]

TypeOK ==
  /\ seq \in [1..MaxSeqLen -> Values]
  /\ orig \in [1..MaxSeqLen -> Values]
  /\ work \subseteq WorkIntervals
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E s \in {x \in [1..MaxSeqLen -> Values] : \E k \in 1..MaxSeqLen : k < Len(x) => x[k] <= x[k+1] /\ Len(x) >= 1} : seq = s
  /\ orig = seq
  /\ work = { [lo |-> 1, hi |-> Len(seq)] }
  /\ pc = "loop"

\* One iteration of the sorting loop: partition an interval strictly
\* larger than one element into two subintervals around a pivot.
LoopStep ==
  /\ pc = "loop"
  /\ \E i \in work :
       /\ work' = (work \ {i}) \cup (IF i.lo = i.hi THEN {} ELSE {LeftInterval(i, i.lo), RightInterval(i.lo, i)})
       /\ \E p \in i.lo..i.hi :
            /\ seq' \in PartitionSeq(seq, i.lo, i.hi)
       /\ pc' = pc
  /\ orig' = orig

Terminate ==
  /\ pc = "loop"
  /\ work = {}
  /\ pc' = "done"
  /\ seq' = seq
  /\ orig' = orig
  /\ work' = work

Quiesce ==
  /\ pc = "done"
  /\ seq' = seq
  /\ orig' = orig
  /\ work' = work
  /\ pc' = pc

Next ==
  \/ LoopStep
  \/ Terminate
  \/ Quiesce

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(LoopStep)
  /\ WF_vars(Terminate)

PCorrect ==
  (pc = "done") =>
    /\ \A f \in {g \in [1..MaxSeqLen -> 1..MaxSeqLen] : \A x \in 1..MaxSeqLen : g[x] \in 1..MaxSeqLen : g[f[x]] = x} : \A x \in 1..MaxSeqLen : seq[x] = orig[f[x]]
    /\ \A x \in 1..(Len(seq) - 1) : seq[x] <= seq[x + 1]

\* The inductive invariant: each sorted interval stays sorted, different
\* intervals never interleave in the domain, and the sequence always
\* stays a permutation of the original input.
Inv ==
  /\ \A i \in WorkIntervals : (i \in work /\ i.lo < i.hi) => \A x \in i.lo..(i.hi - 1) : seq[x] <= seq[x + 1]
  /\ \A i, j \in WorkIntervals : (i \in work /\ j \in work /\ i # j) => (i.hi < j.lo \/ j.hi < i.lo)
  /\ \A f \in {g \in [1..MaxSeqLen -> 1..MaxSeqLen] : \A x \in 1..MaxSeqLen : g[x] \in 1..MaxSeqLen : g[f[x]] = x} : \A x \in 1..MaxSeqLen : seq[x] = orig[f[x]]

Termination ==
  <>(pc = "done")

====