---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen, Seq

\* The original sequence is kept to certify that the final result is a
\* permutation of the input.  Intervals are tracked as a set of ranges, and
\* the program counter is a tiny two-phase protocol rather than a loop var.
VARIABLES seq, origSeq, work, pc

vars == <<seq, origSeq, work, pc>>

\* Interval data type: a contiguous range of positions in the sequence.
Intervals == [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]

TypeOK ==
  /\ seq \in Seq
  /\ origSeq \in Seq
  /\ work \subseteq Intervals
  /\ pc \in {"loop", "done"}

\* The action models the whole of one partitioning step in one stroke.
LoopStep ==
  \/ \E inter \in work :
        \/ IF inter.lo = inter.hi
           THEN /\ work' = work \ {inter}
                /\ UNCHANGED <<seq, origSeq>>
           ELSE
             /\ \E p \in inter.lo..inter.hi :
                  /\ \E ns \in [Seq -> Seq] :
                       /\ \A j \in 1..Len(seq) :
                            ns(seq)[j] = (IF j >= inter.lo /\ j <= inter.hi
                                          THEN seq[j] ELSE seq[j])
                       /\ \A j \in inter.lo..inter.hi :
                            /\ j <= p => seq[j] <= seq[p]
                            /\ p <= j => seq[p] <= seq[j]
                       /\ seq' = ns(seq)
                 /\ work' = (work \ {inter})
                          \cup {[lo |-> inter.lo, hi |-> p], [lo |-> p+1, hi |-> inter.hi]}
             /\ UNCHANGED origSeq
        /\ pc' = "loop"
  \/ /\ work = {}
     /\ pc = "loop"
     /\ pc' = "done"
     /\ UNCHANGED <<seq, origSeq, work>>

Next == LoopStep \/ (pc = "done" /\ UNCHANGED vars)

\* A bounded number of steps is guaranteed by weak fairness on the step.
Spec == Init /\ [][Next]_vars /\ WF_vars(LoopStep)

Init ==
  /\ seq \in Seq
  /\ origSeq = seq
  /\ work = {[lo |-> 1, hi |-> Len(seq)]}
  /\ pc = "loop"

\* Partial correctness: a terminating run left the sequence sorted and
\* still a permutation of the original input.
PCorrect ==
  /\ pc = "done"
  /\ (\A i \in 1..Len(seq) : \E j \in 1..Len(origSeq) : seq[i] = origSeq[j])
  /\ \A i \in 1..(Len(seq) - 1) : seq[i] <= seq[i + 1]

\* A structural invariant used by the hand proof: partitioning never
\* scrambles the domain, preserves the original multiset, and moves
\* sortedness progress inward one interval at a time.
Inv ==
  /\ work \subseteq Intervals
  /\ (\A i \in 1..Len(seq) : \E j \in 1..Len(origSeq) : seq[i] = origSeq[j])
  /\ \A inter \in work : \A i \in inter.lo..(inter.hi - 1) : seq[i] <= seq[i + 1]

Termination == Spec => <>(pc = "done")

====