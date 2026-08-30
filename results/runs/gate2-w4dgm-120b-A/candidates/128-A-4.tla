---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* A finite version of the sequence operator, used to keep the model
\* finite; Sequences is still extended for the indexing operators.
LimitedSeq == CHOOSE seq \in Seq(Vals) :
                 \A i \in DOMAIN seq : seq[i] \in Vals

Vals == Values
Dom == 1..MaxSeqLen
NoSplit == 0
Intervals == {I \in SUBSET Dom : I = {}
                  \/ (\E a, b \in Dom : I = {a..b})}

VARIABLES seq, origSeq, workSet, pc

vars == <<seq, origSeq, workSet, pc>>

TypeOK ==
    /\ seq \in Vals^{(1..MaxSeqLen)}
    /\ origSeq \in Vals^{(1..MaxSeqLen)}
    /\ workSet \subseteq Intervals
    /\ pc \in {"running", "terminated"}

Init ==
    /\ seq \in {s \in Vals^{(1..MaxSeqLen)} : \E k \in 1..MaxSeqLen : Len(s) = k}
    /\ origSeq = seq
    /\ workSet = {1..Len(seq)}
    /\ pc = "running"

\* Partition over one interval: the result set is all valid partitions of
\* that interval (pivot location, elements above and below it), keeping
\* everything outside the interval unchanged.  The action nondeterministically
\* picks one such partition, which is the abstraction over the actual
\* partition procedure.
Partition(i, pivot, leftSeq, rightSeq) ==
    /\ i \in workSet
    /\ i # {}
    /\ Len(i) > 1
    /\ pivot \in i
    /\ leftSeq \in {s \in Vals^{(1..MaxSeqLen)} :
                       \A k \in DOMAIN s : s[k] <= s[pivot]}
    /\ rightSeq \in {s \in Vals^{(1..MaxSeqLen)} :
                        \A k \in DOMAIN s : s[pivot] <= s[k]}
    /\ seq' = [seq EXCEPT ![i] = IF k \in i /\ k <= pivot THEN leftSeq[k]
                                       ELSE IF k \in i /\ k > pivot THEN rightSeq[k]
                                       ELSE @]
    /\ workSet' = (workSet \ {i}) \cup {i \cap (1..pivot), i \cap (pivot + 1..MaxSeqLen)}
    /\ pc' = "running"
    /\ UNCHANGED origSeq

Next ==
    \/ \E i \in Intervals : i \in workSet /\ Len(i) = 1
                               /\ workSet' = workSet \ {i}
                               /\ pc' = "running"
                               /\ UNCHANGED <<seq, origSeq>>
    \/ \E i \in Intervals, p \in Dom, ls, rs \in Vals^{(1..MaxSeqLen)} :
                               Partition(i, p, ls, rs)
    \/ (workSet = {} /\ pc' = "terminated"
        /\ UNCHANGED <<seq, origSeq, workSet>>)
    \/ (pc = "terminated" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars
        /\ \A i \in Intervals, p \in Dom, ls, rs \in Vals^{(1..MaxSeqLen)} :
                     WF_vars(Partition(i, p, ls, rs))

\* A partition leaves everything outside its interval untouched, so the
\* work set at any point is a partition of the domain itself.
IntervalsPartitionDomain ==
    /\ workSet # {}
    /\ \A i \in workSet : i # {}
    /\ (\A i1, i2 \in workSet : i1 # i2 => i1 \cap i2 = {})
    /\ Union(workSet) = Dom

Permutation(s) == \E f \in Permutations(Dom) : s = origSeq \circ f

\* The algorithm builds the sorted sequence one interval at a time, so each
\* interval in the work set is internally sorted relative to the intervals
\* adjacent to it in the domain ordering.
SortProgress ==
    /\ IntervalsPartitionDomain
    /\ (\A i \in workSet : \A a \in i, b \in i : a <= b => seq[a] <= seq[b])

PCorrect == (pc = "terminated") => (Permutation(seq) /\ \A a \in Dom, b \in Dom :
                                          a <= b => seq[a] <= seq[b])

Terminating == (pc = "running") ~> (pc = "terminated")

====