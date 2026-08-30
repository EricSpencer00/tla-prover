---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* A bounded, finite version of the Seq constructor; the config file substitutes
\* this for Seq imported from Sequences so the model stays finite and checkable.
LimitedSeq == [n \in Nat |-> CHOOSE f \in [1..n -> Values] : TRUE]

VARIABLES seq, original, workset, pc
vars == <<seq, original, workset, pc>>

Interval == [l: 1..MaxSeqLen, r: 1..MaxSeqLen]
SeqDom == {1..MaxSeqLen}

TypeOK ==
    /\ seq \in [1..MaxSeqLen -> Values]
    /\ original \in [1..MaxSeqLen -> Values]
    /\ workset \subseteq Interval
    /\ pc \in {"loop", "terminated"}

Init ==
    /\ \E s \in [1..MaxSeqLen -> Values] : seq = s
    /\ original = seq
    /\ workset = {[l |-> 1, r |-> MaxSeqLen]}
    /\ pc = "loop"

\* A partition only reorders elements within the interval and keeps lower parts
\* no greater than upper parts.
PartitionPermutations(a, L, R, p) ==
    { f \in [1..MaxSeqLen -> Values] :
        /\ \A i \in SeqDom : i < L \/ i > R => f[i] = a[i]
        /\ \A i \in L..p, j \in (p + 1)..R : f[i] <= f[j] }

\* One loop iteration: pick an interval, partition it at a pivot, and recurse
\* on the two subintervals.
LoopStep ==
    /\ pc = "loop"
    /\ \E I \in workset :
        /\ workset' = IF I.l = I.r THEN workset \ {I} ELSE workset
        /\ I.l < I.r
           /\ \E pivot \in I.l..I.r :
                /\ \E s \in PartitionPermutations(seq, I.l, I.r, pivot) :
                    seq' = s
                /\ workset' = (workset \ {I})
                        \cup {[l |-> I.l, r |-> pivot], [l |-> pivot + 1, r |-> I.r]}
    /\ UNCHANGED <<original, pc>>

Terminate ==
    /\ pc = "loop"
    /\ workset = {}
    /\ pc' = "terminated"
    /\ UNCHANGED <<seq, original, workset>>

Stall ==
    /\ pc = "terminated"
    /\ UNCHANGED vars

Next == LoopStep \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(LoopStep) /\ WF_vars(Terminate)

\* A terminating run has produced a sorted permutation of the original.
PCorrect ==
    /\ pc = "terminated"
    /\ \E perm \in [1..MaxSeqLen -> 1..MaxSeqLen] :
        /\ \A i \in SeqDom : original[i] = seq[perm[i]]
        /\ \A i, j \in SeqDom : perm[i] < perm[j] => seq[i] <= seq[j]

\* Exact-coverage partitioning of the domain plus permutation preservation.
Inv ==
    /\ /\ (\E c \in [1..MaxSeqLen -> 0..MaxSeqLen] : workset = { [l |-> i, r |-> c[i]] : i \in 1..MaxSeqLen })
       /\ (\A a, b \in workset : a # b => a.r < b.l)
    /\ \A i \in SeqDom : \E j \in SeqDom : seq[i] = original[j]
    /\ \A a, b \in workset : a.r < b.l => (\A i \in a.l..a.r, j \in b.l..b.r : seq[i] <= seq[j])

Termination == <>(pc = "terminated")
====