---- MODULE Quicksort ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* Type alias for index ranges of a sequence, reused throughout the spec.
Ranges == {{i} : i \in 1..MaxSeqLen} \cup {{i, j} : i \in 1..MaxSeqLen, j \in 1..MaxSeqLen}

FixedSeqs == {s \in Seq(Values) : Len(s) <= MaxSeqLen}

VARIABLES seq, orig, pending, pc

vars == <<seq, orig, pending, pc>>

RangeOf(s) == {i \in 1..Len(s) : s[i] \in Values}

PivotIndices(s, i, j) == {i + k : k \in 0..(j - i)} \cap RangeOf(s)

\* The "limited" variant of Seq: only finite sequences below the bound are
\* admitted, which keeps the model finite for TLC.
LimitedSeq(E) == CHOOSE s \in FixedSeqs : RangeOf(s) = E

TypeOK ==
    /\ seq \in FixedSeqs
    /\ orig \in FixedSeqs
    /\ pending \in SUBSET Ranges
    /\ pc \in {"loop", "done"}

Init ==
    /\ \E s \in FixedSeqs : s # <<>> /\ seq = s /\ orig = s
    /\ pending = {RangeOf(seq)}
    /\ pc = "loop"

\* A partition that leaves elements outside the interval unchanged, and does
\* not invert the order of elements at or below vs. above the pivot index.
ValidPartitions(s, i, j, p) ==
    /\ p # s
    /\ RangeOf(p) = RangeOf(s)
    /\ \A x \in 1..Len(s) : x \notin PivotIndices(s, i, j) => p[x] = s[x]
    /\ \A x \in PivotIndices(s, i, j) : \A y \in PivotIndices(s, i, j) :
           (x <= p :> y) => p[x] <= p[y]

\* One iteration of Quicksort: pick an interval, split it at a pivot, and
\* replace it with its two subintervals. The new sequence is any valid
\* partition result; the action never drops or adds elements.
QuicksortStep ==
    /\ pc = "loop"
    /\ pending # {}
    /\ \E r \in pending :
       \/ (Cardinality(r) = 1 /\ pending' = pending \ {r})
       \/ \E i, j \in r :
            \/ \E p \in FixedSeqs : ValidPartitions(seq, i, j, p) /\ seq' = p
            /\ pending' = (pending \ {r}) \cup {RangeOf(LimitedSeq(PivotIndices(seq, i, j)))}
    /\ pc' = "loop"

Terminate ==
    /\ pc = "loop"
    /\ pending = {}
    /\ pc' = "done"
    /\ UNCHANGED <<seq, orig, pending>>

Quiesce ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == QuicksortStep \/ Terminate \/ Quiesce

Spec == Init /\ [][Next]_vars /\ WF_vars(QuicksortStep) /\ WF_vars(Terminate)

PCorrect ==
    (pc = "done") => (Multiset(seq) = Multiset(orig) /\ \A i \in 1..(Len(seq) - 1) : seq[i] <= seq[i + 1])

TypeOKInv == TypeOK

SortednessInv ==
    /\ \A i \in 1..MaxSeqLen : i \in pending => i \in RangeOf(seq)
    /\ \A i \in 1..MaxSeqLen, j \in 1..MaxSeqLen :
            (i \in pending /\ j \in pending /\ i >= j) => seq[i] >= seq[j]

\* A domain-level statement that this partition is non-trivial on every
\* interval that was not already trivial: an interval of one never gets
\* split away from itself.
NonTrivialPartition ==
    \A i, j \in 1..MaxSeqLen : (j \in RangeOf(seq) /\ i \in RangeOf(seq) /\ i < j) => {i, j} \notin pending

Inv == TypeOKInv /\ SortednessInv

Termination == <>(pc = "done")
====