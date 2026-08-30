---- MODULE Quicksort ----
EXTENDS Naturals, Integers, Sequences

CONSTANTS Values, MaxSeqLen

\* A bounded-length wrapper around Seq that keeps the reachable state-space finite.
LimitedSeq == { Seq(f) : f \in [1..MaxSeqLen -> Values] }

\* Permutations are defined via composition with automorphisms of the domain.
Permutations == { g \in [1..MaxSeqLen -> 1..MaxSeqLen] :
                    \A i, j \in 1..MaxSeqLen : g[i] = g[j] => i = j }

\* Partition sequences such that the pivot index separates the two halves and the
\* two halves interleave in no particular order -- any permutation of each half
\* is permitted, which is what makes the choice nondeterministic. Elements
\* outside the interval are untouched.
Partitions(seq, lo, hi, k) == { seq2 \in LimitedSeq :
    /\ \A i \in 1..MaxSeqLen : i < lo \/ i > hi => seq2[i] = seq[i]
    /\ \A i \in lo..hi : \E j \in lo..hi :
        /\ (j <= k <=> i <= k) => seq2[i] = seq[j]
        /\ \A j2 \in lo..hi : (j2 <= k <=> i <= k) => seq2[i] <= seq2[j2] }

VARIABLES seq, origSeq, work, pc
vars == <<seq, origSeq, work, pc>>

Intervals == [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]
Terminating == "done"
Running == "running"

TypeOK ==
    /\ seq \in LimitedSeq /\ origSeq \in LimitedSeq
    /\ work \subseteq Intervals
    /\ pc \in {Running, Terminating}

Init ==
    /\ \E s \in LimitedSeq : seq = s /\ origSeq = s
    /\ work = {[lo |-> 1, hi |-> MaxSeqLen]}
    /\ pc = Running

\* The single action: pick an interval, partition it around a pivot, and
\* replace it with its two subintervals.
SortStep ==
    \/ \E gap \in work :
        /\ work' = work \ {gap}
        /\ pc' = IF work = {gap} THEN Terminating ELSE pc
        /\ UNCHANGED <<seq, origSeq>>
    \/ \E gap \in work, k \in gap.lo..gap.hi :
        /\ k >= gap.lo /\ k < gap.hi
        /\ \E seq2 \in Partitions(seq, gap.lo, gap.hi, k) :
            seq' = seq2
        /\ work' = (work \ {gap}) \cup {[lo |-> gap.lo, hi |-> k], [lo |-> k+1, hi |-> gap.hi]}
        /\ pc' = pc
    \/ (pc = Terminating /\ UNCHANGED vars)

\* Loop-free final-state self-loop so the model never deadlocks once done.
Stuttering == pc = Terminating /\ UNCHANGED vars

Next == SortStep \/ Stuttering

Spec == Init /\ [][Next]_vars
    /\ WF_vars(SortStep) /\ WF_vars(Stuttering)

\* Termination: when the algorithm is done it has produced a sorted copy of the
\* original data.
PCorrect == (pc = Terminating) => (seq \in Permutations[origSeq] /\ \A i \in 1..MaxSeqLen-1 : seq[i] <= seq[i+1])

\* The whole point of the model: the work set is always a partition of the sorted
\* region, so no interval is ever dropped or overlapped and no element is left
\* unprocessed or double-processed.
Inv ==
    /\ work \subseteq { [lo |-> lo, hi |-> hi] : 1 <= lo <= hi <= MaxSeqLen }
    /\ \A g, h \in work : (g.hi + 1 >= h.lo /\ h.lo <= g.hi + 1) => g = h
    /\ \A i \in 1..MaxSeqLen : (\E g \in work : g.lo <= i /\ i <= g.hi) \/ (seq[i] = origSeq[i])
    /\ \A g \in work : \A i \in g.lo..g.hi : \A j \in g.lo..g.hi : i < j => seq[i] <= seq[j]

Termination == <>(pc = Terminating)

\* The invariant is also checked at every reachable state, not just at the end.
TypeOKInv == TypeOK /\ Inv
====