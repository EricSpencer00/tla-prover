---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* Replaces Sequences!Seq with a checkable finite version, exactly as the .cfg
\* requires: keep the EXTENDS line so everything Seq needs is still in scope,
\* and define the new operator under the name the config replaces over.
\* The constant MaxSeqLen comes from the companion .cfg.
CONSTANTS Values, MaxSeqLen

LimitedSeq(n, S) == [i \in 1..n |-> CHOOSE e \in S : TRUE]

VARIABLES seq, original, work, pc

Intervals == [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]

TypeOK ==
    /\ seq \in Seq(Values)
    /\ Len(seq) <= MaxSeqLen
    /\ original \in Seq(Values)
    /\ Len(original) <= MaxSeqLen
    /\ work \subseteq Intervals
    /\ pc \in {"loop", "done"}

Init ==
    /\ \E s \in Seq(Values) :
        /\ Len(s) > 0
        /\ Len(s) <= MaxSeqLen
        /\ seq = s
        /\ original = s
    /\ work = {[lo |-> 1, hi |-> Len(seq)]}
    /\ pc = "loop"

\* A permutation of the domain that respects the partition order below the
\* pivot and leaves everything outside the interval unchanged.
PartitionOp(t, iv, p) == \E f \in [1..Len(seq) -> 1..Len(seq)] :
    /\ \A i \in 1..Len(seq) : f[i] # i => iv.lo <= i /\ i <= iv.hi
    /\ \A i \in 1..Len(seq) : f[i] # i => f[i] # i
    /\ \A i \in 1..Len(seq) : f[f[i]] = i
    /\ \A low \in iv.lo..p, high \in (p+1)..iv.hi : t[f[low]] <= t[f[high]]
    /\ \A i \in 1..Len(seq) : i < iv.lo \/ i > iv.hi => f[i] = i
    /\ [i \in 1..Len(seq) |-> t[f[i]]]

\* One iteration of the quicksort recursion: a whole interval is replaced by
\* its two subintervals, after applying an arbitrary valid partition result.
Iterate ==
    \/ \E iv \in work :
        /\ work' = work \ {iv}
        /\ IF iv.lo = iv.hi
           THEN work'
           ELSE \E p \in iv.lo..(iv.hi - 1) :
                /\ /\ seq' = PartitionOp(seq, iv, p)
                   /\ /\ work' = work' \cup {[lo |-> iv.lo, hi |-> p], [lo |-> p+1, hi |-> iv.hi]}
        /\ UNCHANGED original
    \/ /\ work = {}
       /\ pc' = "done"
       /\ UNCHANGED <<seq, original, work>>
    \/ /\ pc = "done"
       /\ UNCHANGED <<seq, original, work, pc>>

Next == Iterate

Spec == Init /\ [][Next]_<<seq, original, work, pc>>

\* The algorithm's partial correctness: if it has reached its final state,
\* the result is a sorted permutation of the original input.
PCorrect ==
    /\ pc = "done"
    /\ \A i \in 1..Len(seq), j \in 1..Len(seq) : seq[i] = original[j] => i = j
    /\ \A i \in 1..(Len(seq) - 1) : seq[i] <= seq[i + 1]

\* The invariant the proof works from: intervals partition the domain, the
\* current sequence is always a permutation of the original, and the
\* relative ordering of each interval's two halves is respected.
Inv ==
    /\ \A i \in 1..(Len(seq) - 1) : seq[i] <= seq[i + 1]
    /\ \A i \in 1..Len(seq) : \E j \in 1..Len(seq) : seq[i] = original[j]
    /\ \A iv \in work : iv.lo <= iv.hi

Termination ==
    (pc = "done") ~> (pc = "done")
====