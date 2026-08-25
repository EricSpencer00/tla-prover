---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* Finite version of Seq for model checking
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\* ----------------------------------------------------------------------
\* State variables
VARIABLES seq, orig, work, pc

vars == << seq, orig, work, pc >>

\* ----------------------------------------------------------------------
\* Helper definitions
Interval(i) == i
IntervalLo(i) == i[1]
IntervalHi(i) == i[2]

CountInInterval(s, lo, hi, v) ==
  Cardinality({ j \in lo..hi : s[j] = v })

Permutation(s, t) ==
  \A v \in Values : CountInInterval(s, 1, Len(s), v) = CountInInterval(t, 1, Len(t), v)

Sorted(s) ==
  \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

\* Partition operator: all sequences that could result from a correct partition
Partition(seq, i, p) ==
  { newseq \in LimitedSeq(Values) :
      /\ Len(newseq) = Len(seq)
      /\ \A j \in 1..Len(seq) :
           (j < IntervalLo(i) \/ j > IntervalHi(i)) => newseq[j] = seq[j]
      /\ \A v \in Values :
           CountInInterval(seq, IntervalLo(i), IntervalHi(i), v) =
           CountInInterval(newseq, IntervalLo(i), IntervalHi(i), v)
      /\ \A j \in IntervalLo(i)..p, k \in p+1..IntervalHi(i) :
           newseq[j] <= newseq[k] }

\* ----------------------------------------------------------------------
\* Initial state
Init ==
  /\ seq \in LimitedSeq(Values)
  /\ Len(seq) > 0
  /\ orig = seq
  /\ work = { << 1, Len(seq) >> }
  /\ pc = "Loop"

\* ----------------------------------------------------------------------
\* Actions
StepSingle ==
  /\ pc = "Loop"
  /\ work # {}
  /\ \E i \in work :
       LET lo == IntervalLo(i) IN hi == IntervalHi(i) IN
       /\ lo = hi
       /\ work' = work \ {i}
       /\ seq'  = seq
       /\ orig' = orig
       /\ pc'   = "Loop"

StepPartition ==
  /\ pc = "Loop"
  /\ work # {}
  /\ \E i \in work :
       LET lo == IntervalLo(i) IN hi == IntervalHi(i) IN
       /\ lo < hi
       /\ \E p \in lo..hi :
            /\ \E newseq \in Partition(seq, i, p) :
                 /\ seq'  = newseq
       /\ work' = (work \ {i}) \cup { << lo, p >> , << p+1, hi >> }
       /\ orig' = orig
       /\ pc'   = "Loop"

StepDone ==
  /\ pc = "Loop"
  /\ work = {}
  /\ pc' = "Done"
  /\ UNCHANGED << seq, orig, work >>

StepStutter ==
  /\ pc = "Done"
  /\ UNCHANGED << seq, orig, work, pc >>

Next ==
  \/ StepSingle
  \/ StepPartition
  \/ StepDone
  \/ StepStutter

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
TypeOK ==
  /\ seq \in LimitedSeq(Values)
  /\ orig \in LimitedSeq(Values)
  /\ Len(seq) = Len(orig)
  /\ work \subseteq { << lo, hi >> : lo \in 1..Len(seq) /\ hi \in lo..Len(seq) }
  /\ pc \in {"Loop", "Done"}

\* ----------------------------------------------------------------------
\* Main invariant (preservation of permutation)
Inv == Permutation(seq, orig)

\* ----------------------------------------------------------------------
\* Partial correctness when terminated
PCorrect ==
  /\ pc = "Done"
  => /\ Sorted(seq)
     /\ Permutation(seq, orig)

\* ----------------------------------------------------------------------
\* Liveness property (termination)
Termination == <> (pc = "Done")

\* ----------------------------------------------------------------------
\* Exported identifiers
\* (the .cfg file will refer to these names)
\* SPECIFICATION: Spec
\* INVARIANTS: PCorrect, TypeOK, Inv
\* PROPERTIES: Termination

====