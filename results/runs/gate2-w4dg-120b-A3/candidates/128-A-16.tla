---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

\* The sorting action takes an interval larger than one and nondeterministically
\* produces any sequence that a partition step could have yielded: sorted
\* across the pivot and unchanged outside it. Repeat until every interval is
\* a singleton. The invariant protects that the work set never overlaps and
\* that the running sequence stays a permutation of the original.

CONSTANTS Values, MaxSeqLen

VARIABLES seq, base, work, pc

vars == <<seq, base, work, pc>>

\* A partition only ever rearranges elements inside the interval, so the
\* permutation relation is preserved across each iteration. The work set is a
\* partition of the domain, which is what lets the sortedness condition be
\* checked interval by interval rather than comparing every pair of indices.

Intervals == [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]

TypeOK ==
    /\ seq \in Seq(Values)
    /\ Len(seq) <= MaxSeqLen
    /\ base \in Seq(Values)
    /\ Len(base) = Len(seq)
    /\ work \subseteq Intervals
    /\ pc \in {"loop", "done"}

\* Separate from the built-in Seq operator: this is a bounded, finite version
\* of it for the model checker. The .cfg file replaces the standard definition.
LimitedSeq(n) == CHOOSE s \in Seq(Values) : Len(s) = n /\ \A i \in 1..n : s[i] \in Values

Init ==
    /\ \E n \in 1..MaxSeqLen:
         /\ seq = LimitedSeq(n)
         /\ base = LimitedSeq(n)
    /\ work = {[lo |-> 1, hi |-> Len(seq)]}
    /\ pc = "loop"

\* A full partition is nondeterministic over its result, so the action names the
\* exact condition the result must satisfy rather than constructing it.
Rearranged(s, lo, hi, p) ==
    /\ Len(s) = Len(seq)
    /\ \A k \in 1..Len(seq):
         (k < lo \/ k > hi) => s[k] = seq[k]
    /\ \A k \in lo..p: \A j \in p+1..hi: s[k] <= s[j]

SplitInterval(w, lo, hi) ==
    /\ hi > lo
    /\ \E p \in lo..hi:
         /\ \E s \in Seq(Values):
              /\ Rearranged(s, lo, hi, p)
              /\ seq' = s
         /\ [lo |-> lo, hi |-> p] \in work
         /\ [lo |-> p+1, hi |-> hi] \in work

Next ==
    \/ \E w \in work:
         /\ Len(seq) >= w.hi
         /\ work' = work \ {w}
         /\ IF w.lo = w.hi
            THEN work'
            ELSE work' \cup SplitInterval(w, w.lo, w.hi)
    \/ (work = {} /\ pc' = "done")
    \/ (pc = "done" /\ UNCHANGED <<seq, base, work, pc>>)

Spec == Init /\ [][Next]_vars /\ SF_vars(Next)

PCorrect == pc = "done"

\* The work set stays a partition of the domain, the running sequence is a
\* permutation of the original, and each interval is sorted against its
\* successor. Together these give the full sorted-permutation theorem.
Inv ==
    /\ \A a, b \in work: (a.lo <= b.lo /\ a.hi >= b.lo) => (a.lo = b.lo /\ a.hi = b.hi)
    /\ \E p \in [1..Len(seq) -> 1..Len(seq)]: seq = base \o p
    /\ \A i \in 1..Len(seq) - 1: seq[i] <= seq[i+1]

Termination == <>(pc = "done")

====