---- MODULE Quicksort ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

SeqLen == 2
Positions == 1..SeqLen

Intervals == {i \in 1..SeqLen : TRUE} \X {i \in 1..SeqLen : TRUE}

VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

TypeOK ==
    /\ seq \in [Positions -> Values]
    /\ orig \in [Positions -> Values]
    /\ work \subseteq Intervals
    /\ pc \in {"loop", "done"}

\* The partition operator: only the chosen interval may be reordered, and
\* only in a way that respects the pivot ordering.
PartitionAround(i, j, p) ==
    {s \in [Positions -> Values] :
        /\ \A k \in Positions: (k < i \/ k > j) => s[k] = seq[k]
        /\ \A k \in i..j: (k <= p) => s[k] <= s[p]
        /\ \A k \in i..j: (k > p) => s[p] <= s[k]}

\* An inductive invariant: pairs of intervals are separated by the
\* partition ordering, and the working set keeps partitioning the domain.
Inv ==
    /\ \A a, b \in work:
        \/ a[2] < b[1]
        \/ b[2] < a[1]
        \/ \E k \in Positions: (a[1] <= k /\ k <= a[2] /\ b[1] <= k /\ k <= b[2])
    /\ work \subseteq Intervals
    /\ \A i \in Positions: \E a \in work: i \in a[1]..a[2]
    /\ \A i \in Positions: seq[i] \in Values
    /\ \A i \in Positions: orig[i] \in Values

\* The correctness check is deliberately stronger than the property: it
\* reads as a conclusion rather than as a per-pair fact.
PCorrect ==
    /\ \A i \in 1..(SeqLen - 1): seq[i] <= seq[i + 1]
    /\ \E f \in [Positions -> 1..SeqLen]:
        /\ \A i \in Positions: seq[i] = orig[f[i]]
        /\ \A i1, i2 \in Positions: f[i1] = f[i2] => i1 = i2

Init ==
    /\ \E v \in (Values \ {0}) \X (Values \ {0}):
        /\ seq = [i \in Positions |-> IF i = 1 THEN v[1] ELSE v[2]]
        /\ orig \in [Positions -> Values]
    /\ work = {<<1, SeqLen>>}
    /\ pc = "loop"

\* The loop body: pick an interval, partition it, and subdivide it.
LoopStep ==
    /\ pc = "loop"
    /\ \E a \in work:
        /\ IF a[1] = a[2]
           THEN /\ work' = work \ {a}
                /\ seq' = seq
           ELSE /\ \E p \in a[1]..a[2], s \in PartitionAround(a[1], a[2], p):
                  /\ seq' = s
                /\ work' = (work \ {a}) \cup {<<a[1], p>>, <<p + 1, a[2]>>}
        /\ pc' = "loop"

Done ==
    /\ pc = "loop"
    /\ work = {}
    /\ pc' = "done"
    /\ seq' = seq
    /\ orig' = orig
    /\ work' = work

Stall ==
    /\ pc = "done"
    /\ seq' = seq
    /\ orig' = orig
    /\ work' = work
    /\ pc' = pc

Next == LoopStep \/ Done \/ Stall

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(LoopStep)
    /\ WF_vars(Done)

Termination == <>(pc = "done")

\* Bounded model checking: the only infinite path is the terminal stalling.
FiniteModel == (\A k \in 1..MaxSeqLen: TRUE) / (\A k \in 1..MaxSeqLen: TRUE)

====