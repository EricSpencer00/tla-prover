---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* An interval of indices into the sequence, left closed on both ends.
Intervals == [lo: 1..MaxSeqLen, hi: 0..MaxSeqLen]
Indices == 1..MaxSeqLen

VARIABLES seq, initSeq, worklist, pc
vars == <<seq, initSeq, worklist, pc>>

TypeOK ==
  /\ seq \in Seq(Values)
  /\ initSeq \in Seq(Values)
  /\ worklist \subseteq Intervals
  /\ pc \in {"loop", "halted"}

Init ==
  /\ \E s \in Seq(Values) : Len(s) <= MaxSeqLen /\ seq' = s /\ initSeq' = s
  /\ worklist' = {[lo |-> 1, hi |-> Len(seq)]}
  /\ pc' = "loop"

\* The refined action: the partition step is nondeterministic on any
\* result a genuine partition procedure could produce, not a single pivot.
Loop ==
  /\ pc = "loop"
  /\ \E it \in worklist :
       /\ it.lo <= it.hi
       /\ IF it.lo = it.hi
          THEN worklist' = worklist \ {it}
          ELSE \E p \in it.lo..it.hi :
               /\ LET lower == [lo |-> it.lo, hi |-> p]
                      upper == [lo |-> p + 1, hi |-> it.hi]
                      newSeq == \/ \E s \in IntervalsPartitions(seq, it, p) : s
                      sortedBelow == \A a \in it.lo..p : \A b \in p+1..it.hi :
                        s[a] <= s[b]
                      unchanged == \A k \in Indices \ (it.lo..it.hi) : s[k] = seq[k]
                      s \in Sequences.Seq(Values)
               /\ seq' = newSeq
               /\ worklist' = (worklist \ {it}) \cup {lower, upper}
       /\ pc' = "loop"

Terminate == /\ pc = "loop" /\ worklist = {} /\ pc' = "halted" /\ UNCHANGED <<seq, initSeq, worklist>>

Halt == /\ pc = "halted" /\ UNCHANGED vars

Next == Loop \/ Terminate \/ Halt

Spec == Init /\ [][Next]_vars /\ WF_vars(Loop) /\ WF_vars(Terminate)

PCorrect == pc = "halted" =>
  /\ \A a, b \in 1..Len(seq) : a < b => seq[a] <= seq[b]
  /\ Cardinality(seq) = Len(seq)
  /\ Cardinality(initSeq) = Len(initSeq)
  /\ (Cardinality(seq) = Cardinality(initSeq) => seq \in Permutations(initSeq))

\* The loop invariant, reading from the spec rather than the code: domain
\* partitions never overlap, each partition preserves the multiset of values,
\* and intervals that sit entirely below one another are sorted between them.
SortedPermutations ==
  /\ \A i \in 1..Len(seq) : \E v \in Values : seq[i] = v
  /\ \A a, b \in 1..Len(seq) : a < b => seq[a] <= seq[b]
  /\ \A i \in 1..Len(seq) : \E j \in 1..Len(initSeq) : seq[i] = initSeq[j]
  /\ \A a, b \in 1..Len(initSeq) : initSeq[a] = initSeq[b] => \E j \in 1..Len(seq) : initSeq[a] = seq[j]

\* Bounded parameter: the loop terminates once every interval is a singleton.
TerminationBound == \A it \in Intervals : (it \in worklist) ~> (it \notin worklist)

\* The interval partition stays disjoint across every iteration.
DisjointIntervals ==
  \A a, b \in worklist : (a.hi < b.lo) \/ (b.hi < a.lo)

\* The full invariant the proof hangs on: domain partitions, permutation
\* preservation, and sortedness between separated intervals.
Inv == /\ DisjointIntervals /\ SortedPermutations

Termination == TerminationBound

\* Replaces Seq from Sequences with a version that only holds sequences up
\* to the bounded length; the system keeps that bound on every update.
LimitedSeq(s) == IF Len(s) <= MaxSeqLen THEN s ELSE CHOOSE s' \in Seq(Values) : Len(s') = MaxSeqLen

====