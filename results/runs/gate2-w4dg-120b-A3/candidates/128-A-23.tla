---- MODULE Quicksort ----
EXTENDS Naturals, Sequences

\* Each action (SortStep and Terminate) is given partial fairness; the
\* stuttering step is there so the spec never deadlocks once it has
\* terminated (the fairness constraints keep it from being chosen).
\* The operator LimitedSeq is defined at the bottom by the .cfg file.

CONSTANTS Values, MaxSeqLen

\* A permutation of a domain is given as an automorphism of that domain.
Permutation(S) ==
  {f \in [1..MaxSeqLen -> 1..MaxSeqLen] : \A x \in S : f[x] \in S}

InDomain == {i \in 1..MaxSeqLen : i <= Len(seq)}
AtOrBelow(i) == {j \in 1..MaxSeqLen : j <= i}
Above(i) == {j \in 1..MaxSeqLen : j > i}

\* Any partition that leaves elements outside the interval unchanged,
\* and puts everything at or below the pivot no greater than everything
\* above it, is a possible outcome of that interval's partition step.
NondeterministicPartition(seq, i) ==
  {seq2 \in Permutation(InDomain) :
     \A j \in 1..MaxSeqLen :
       (j \notin AtOrBelow(i) \cup Above(i)) => seq2[j] = seq[j]
       /\ (j \in AtOrBelow(i) /\ k \in Above(i)) => seq2[j] <= seq2[k]}

VARIABLES seq, origSeq, workSet, pc

vars == <<seq, origSeq, workSet, pc>>

Intervals == {I \in SUBSET (1..MaxSeqLen):
                \E lo, hi \in 1..MaxSeqLen : I = {k \in 1..MaxSeqLen : lo <= k <= hi}}

TypeOK ==
  /\ seq \in Values^{0..MaxSeqLen}
  /\ origSeq \in Values^{0..MaxSeqLen}
  /\ workSet \subseteq Intervals
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E s \in Values^{1..MaxSeqLen} :
       /\ Len(s) <= MaxSeqLen
       /\ seq = s
       /\ origSeq = s
  /\ workSet = {1..MaxSeqLen}
  /\ pc = "loop"

\* One sorting iteration: either remove a singleton interval, or split
\* a larger interval around a pivot and apply a possible partition.
SortStep ==
  /\ pc = "loop"
  /\ workSet # {}
  /\ \E i \in workSet :
       /\ LET lo == CHOOSE k \in i : \A m \in i : k <= m
            hi == CHOOSE k \in i : \A m \in i : m <= k
          IN
            \/ /\ lo = hi
               /\ workSet' = workSet \ {i}
               /\ UNCHANGED <<seq, origSeq>>
            \/ /\ lo < hi
               /\ \E p \in lo..hi :
                    /\ seq' \in NondeterministicPartition(seq, p)
                    /\ workSet' = (workSet \ {i}) \cup {lo..p} \cup {p+1..hi}
               /\ UNCHANGED origSeq
  /\ UNCHANGED pc

Terminate ==
  /\ pc = "loop"
  /\ workSet = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, origSeq, workSet>>

Next ==
  \/ SortStep
  \/ Terminate
  \/ /\ pc = "done"
     /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars
          /\ WF_vars(SortStep)
          /\ WF_vars(Terminate)

\* The full correctness theorem: termination implies the result is a
\* sorted permutation of the input.
PCorrect ==
  (pc = "done") => (\A i \in 1..MaxSeqLen : origSeq[i] = seq[i])
    /\ (\A i \in 1..(MaxSeqLen - 1) : seq[i] <= seq[i+1])

\* An inductive invariant, kept as a named fact for the partial proof
\* (the proof itself is not written out in this file).
Inv ==
  /\ \A i \in 1..MaxSeqLen : origSeq[i] = seq[i]
  /\ \A i \in 1..(MaxSeqLen - 1) : seq[i] <= seq[i+1]

Termination == pc = "done"

====