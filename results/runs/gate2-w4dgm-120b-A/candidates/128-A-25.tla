---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* The partition operator is the nondeterministic choice modelling
\* "any valid partition a real partition procedure could produce".
Partition(seq, lo, hi, p) ==
  { q \in seq :
       /\ \A i \in 1 .. Len(seq) : (i < lo \/ i > hi) => q[i] = seq[i]
       /\ \A i \in lo .. p : \A j \in p + 1 .. hi :
            q[i] <= q[j] }

\* The model is tiny, so the interval set is kept unordered and the
\* reduction relation is weakly fair on it rather than on a queue.
Intervals == UNION {[lo, hi] : lo, hi \in 1 .. MaxSeqLen}

\* One action, two cases inside it; the case distinction is exactly
\* what forces the run to terminate once all intervals are singletons.
VARIABLES seq, orig, work, pc

vars == << seq, orig, work, pc >>

TypeOK ==
  /\ seq \in Seq(Values)
  /\ orig \in Seq(Values)
  /\ work \subseteq Intervals
  /\ pc \in {"loop", "done"}

Init ==
  /\ seq \in [1 .. MaxSeqLen -> Values]
  /\ orig = seq
  /\ work = {[1, MaxSeqLen]}
  /\ pc = "loop"

Step ==
  /\ pc = "loop"
  /\ work # {}
  /\ \E I \in work :
       IF I[1] = I[2]
       THEN work' = work \ {I}
       ELSE
         /\ \E p \in I[1] .. I[2] :
              /\ LET lo == I[1] uphi == p + 1, hi == I[2] IN
                 /\ work' = (work \ {I}) \cup {[lo, p], [p + 1, hi]}
                 /\ seq' = CHOOSE q \in Partition(seq, lo, hi, p) : TRUE
       /\ pc' = pc
  /\ orig' = orig

Terminate ==
  /\ pc = "loop"
  /\ work = {}
  /\ pc' = "done"
  /\ seq' = seq
  /\ orig' = orig
  /\ work' = work

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == Step \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Step) /\ WF_vars(Terminate)

SortedPermutation ==
  /\ \A i \in 1 .. Len(seq) : \E j \in 1 .. Len(orig) : seq[i] = orig[j]
  /\ \A i \in 1 .. Len(seq) - 1 : seq[i] <= seq[i + 1]

SoftwarePartition ==
  /\ work # {}
  /\ \A I \in work :
       \A i \in I[1] .. I[2] : \A j \in I[2] + 1 .. Len(seq) : seq[i] <= seq[j]

PCorrect == pc = "done" => SortedPermutation

\* The invariant is partitioned by interval rather than monolithic, so
\* it stays strongly satisfied instead of just being forced true at the
\* end by the SortedPermutation property.
Inv ==
  /\ SoftwarePartition
  /\ \A i \in 1 .. Len(seq) : \E j \in 1 .. Len(orig) : seq[i] = orig[j]

Termination == <>(pc = "done")

\* Models the bounded runtime's version of the sequence operator.
FINITE == TRUE
\* The operator the .cfg file redefines to keep the model finite.
LimitedSeq(f, S) == SelectSeq(f, S)
====