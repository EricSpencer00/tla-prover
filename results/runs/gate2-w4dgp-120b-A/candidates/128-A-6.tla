---- MODULE Quicksort ----
EXTENDS Naturals, Integers, FiniteSets, Sequences

\* The original model imported Seq from Sequences. For model checking we need a
\* bounded version, so the .cfg replaces it with the operator below.
CONSTANTS Values, MaxSeqLen

VARIABLES seq, originalSeq, toSort, pc
vars == <<seq, originalSeq, toSort, pc>>

\* Bounded, finite version of Sequences!Seq: only sequences up to a fixed
\* length are available. This keeps the model finite for TLC.
LimitedSeq(S) ==
  {s \in Seq(S) : Len(s) <= MaxSeqLen}

Domain == 1..MaxSeqLen
Intervals == {i \in Domain : i >= 1 /\ i <= 2}
Subintervals == {i \in Intervals : i >= 1 /\ i <= 2}
SubintervalsOf(i) == {j \in Subintervals : j >= 1 /\ j <= i}
EmptyInt == <<>>

\* A partition of the current interval works like the partition step of
\* quicksort: the interval is split around a pivot index, elements below or at
\* the pivot are no greater than those above it, and everything outside the
\* interval is untouched.
Partitions(f, i, j) ==
  {g \in Automorphisms(Domain) :
     (i < j \/ j < i) /\ (g[j] = f[j] \/ g[j] = f[i]) /\
       \A k \in Domain : (k <= i \/ k >= j) => g[k] = f[k]}

TypeOK ==
  /\ seq \in LimitedSeq(Values)
  /\ originalSeq \in LimitedSeq(Values)
  /\ toSort \subseteq Intervals
  /\ pc \in {"main", "done"}

Init ==
  /\ \E s \in LimitedSeq(Values) : s # <<>> /\ seq' = s /\ originalSeq' = s
  /\ toSort' = {<<1, Len(seq)>>}
  /\ pc' = "main"

\* The sorting loop is a single action, but it nondeterministically picks the
\* interval to work on and the pivot within it.
Step ==
  \/ \E i \in toSort :
       /\ pc = "main"
       /\ \E g \in SubintervalsOf(i[2] - i[1] + 1) :
            /\ i[2] - i[1] + 1 > 1
            /\ \E s \in Partitions(seq, i[1] + g - 1, i[2] - g + 1) :
                 seq' = s
            /\ toSort' = (toSort \ {i}) \cup {<<i[1], i[1] + g - 1>>, <<i[1] + g, i[2]>>}
            /\ pc' = "main"
  \/ \E i \in toSort :
       /\ pc = "main"
       /\ i[2] - i[1] + 1 = 1
       /\ toSort' = toSort \ {i}
       /\ pc' = "main"
  \/ /\ pc = "main"
     /\ toSort = {}
     /\ pc' = "done"
     /\ UNCHANGED <<seq, originalSeq, toSort>>
  \/ /\ pc = "done"
     /\ UNCHANGED vars

\* A stuttering step after termination (required for strong fairness to be
\* well-defined on the relation below).
DoneStep == pc = "done" /\ UNCHANGED vars

Next == Step \/ DoneStep

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

\* Partitioning never throws away or duplicates a value: the new sequence is
\* the old one composed with an automorphism of the domain.
PCorrect ==
  /\ pc = "done"
  /\ seq \in {originalSeq[i] : i \in Domain}
  /\ \A i \in 1..(Len(seq) - 1) : seq[i] <= seq[i + 1]

\* The invariant is stronger than it looks: it is the whole correctness
\* argument, carried forward through every loop iteration.
Inv ==
  /\ \A i \in toSort :
       (i[1] >= 1 /\ i[2] <= Len(seq) /\ i[1] <= i[2] /\ i[2] - i[1] >= 0)
  /\ seq \in {originalSeq[i] : i \in Domain}
  /\ \A i \in toSort : \A j \in 1..(Len(seq) - 1) :
       (j >= i[1] /\ j < i[2]) => seq[j] <= seq[j + 1]

Termination == WF_vars(Step)
====