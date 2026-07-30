---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets

\* One interval is a contiguous range of indices; intervals are identified by
\* the pair of endpoints and are always non-empty.
Interval == [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]

\* The partition operator abstracts away the actual partition algorithm: it
\* chooses any new sequence that is a valid partition of the current one
\* over the chosen interval and pivot. A partition leaves everything
\* outside the interval untouched, and every element in the lower piece is
\* no greater than every element in the upper piece.
SeqPartition(s, intv, p) ==
  { sPrime \in [1..MaxSeqLen -> Values] :
      \A i \in 1..MaxSeqLen :
        (i < intv.lo \/ i > intv.hi) => sPrime[i] = s[i]
      /\ \A i \in intv.lo..p, j \in p+1..intv.hi : sPrime[i] <= sPrime[j] }

CONSTANTS Values, MaxSeqLen, Seq

VARIABLES seq, origSeq, workSet, pc
vars == << seq, origSeq, workSet, pc >>

TypeOK ==
  /\ seq \in [1..MaxSeqLen -> Values]
  /\ origSeq \in [1..MaxSeqLen -> Values]
  /\ workSet \subseteq Interval
  /\ pc \in {"running", "done"}

Init ==
  /\ seq = Seq
  /\ origSeq = Seq
  /\ workSet = {[lo |-> 1, hi |-> MaxSeqLen]}
  /\ pc = "running"

\* Any interval in the work set that has collapsed to a point can be dropped.
DropSingleton ==
  /\ \E intv \in workSet :
       /\ intv.lo = intv.hi
       /\ workSet' = workSet \ {intv}
  /\ UNCHANGED << seq, origSeq, pc >>

\* Selecting an interval and a pivot index, then picking any valid partitioning
\* of the current sequence over that interval according to the operator.
PartitionStep ==
  /\ \E intv \in workSet :
       /\ intv.lo < intv.hi
       /\ \E p \in intv.lo..intv.hi :
            /\ \E sPrime \in SeqPartition(seq, intv, p) :
                 seq' = sPrime
            /\ lower == [lo |-> intv.lo, hi |-> p]
            /\ upper == [lo |-> p + 1, hi |-> intv.hi]
            /\ workSet' = (workSet \ {intv}) \cup {lower, upper}
  /\ UNCHANGED << origSeq, pc >>

Terminate ==
  /\ workSet = {}
  /\ pc = "running"
  /\ pc' = "done"
  /\ UNCHANGED << seq, origSeq, workSet >>

QuicksortStep == DropSingleton \/ PartitionStep

Next == QuicksortStep \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(QuicksortStep)

\* The invariant is a conjunction of three parts: a partition of the domain
\* into the work-set intervals plus the singleton points, preservation of
\* the multiset of elements, and relative ordering between intervals.
Inv ==
  /\ (\A intv \in workSet : intv.lo <= intv.hi)
  /\ (\A i \in 1..MaxSeqLen : \E j \in 1..MaxSeqLen : seq[i] = origSeq[j])
  /\ (\A a, b \in workSet :
        (a.hi <= b.lo /\ a.hi < MaxSeqLen) => seq[a.hi] <= seq[b.lo])

PCorrect == pc = "done" => (\A i \in 1..MaxSeqLen-1 : seq[i] <= seq[i + 1])
Termination == <>(pc = "done")
====