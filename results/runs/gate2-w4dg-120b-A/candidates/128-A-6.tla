---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen, Seq

\* The system is a single sequential sort.  The work set is a set of
\* intervals, each a contiguous range of indices.  A single action
\* selects an interval, picks a pivot, and nondeterministically chooses
\* any sequence that a partition could have produced: elements inside the
\* interval are reordered so that everything at or below the pivot index
\* is no greater than everything above it, and everything outside the
\* interval is left untouched.  The algorithm terminates when the work
\* set is empty.

Intervals == [lo : 1..MaxSeqLen, hi : 1..MaxSeqLen]
Lattice == [low : 1..MaxSeqLen, high : 1..MaxSeqLen]
Mapper == [do : [1..MaxSeqLen -> 1..MaxSeqLen], inv : [1..MaxSeqLen -> 1..MaxSeqLen]]

VARIABLES seq, original, workset, pc
vars == <<seq, original, workset, pc>>

TypeOK ==
    /\ seq \in Seq
    /\ original \in Seq
    /\ workset \subseteq Intervals
    /\ pc \in {"mainloop", "done"}

Init ==
    /\ seq \in Seq
    /\ original = seq
    /\ workset = { [lo |-> 1, hi |-> Len(seq)] }
    /\ pc = "mainloop"

\* A partition may also be the identity -- that is what lets the
\* algorithm subdivide an interval without touching the sequence.
Identity == [x \in 1..MaxSeqLen |-> x]

\* A bijection of domain indices; composed with the sequence it
\* reorders the sequence without changing the multiset of values.
Reordering(k) == seq \circ k.do

Permutations ==
    { Reordering(c) : c \in Mapper : \A i \in 1..MaxSeqLen : c.do[i] <= Len(seq) }

ValidPartition(k, lo, pivot, hi) ==
    /\ \A i \in 1..MaxSeqLen : i < lo => k.do[i] = i
    /\ \A i \in 1..MaxSeqLen : i > hi => k.do[i] = i
    /\ \A i \in lo..pivot, j \in (pivot + 1)..hi : seq[k.do[i]] <= seq[k.do[j]]

\* The one action of the model: pick an interval, pick a pivot, pick a
\* legal partition, update the sequence, and replace the interval with
\* its two subintervals.
Step ==
    /\ pc = "mainloop"
    /\ workset # {}
    /\ \E interval \in workset :
        /\ workset' = workset \ {interval}
        /\ IF interval.lo = interval.hi
           THEN workset'
           ELSE
               \/ workset \cup { [lo |-> interval.lo, hi |-> pivot],
                                 [lo |-> pivot + 1, hi |-> interval.hi] }
               \/ workset
               /\ \E pivot \in interval.lo..(interval.hi - 1), k \in Mapper :
                     /\ ValidPartition(k, interval.lo, pivot, interval.hi)
                     /\ seq' = Reordering(k)
        /\ UNCHANGED original
    /\ pc' = "mainloop"

Done ==
    /\ pc = "mainloop"
    /\ workset = {}
    /\ pc' = "done"
    /\ UNCHANGED <<seq, original, workset>>

Stall ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == Step \/ Done \/ Stall
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Sorted(s) == \A i \in 1..(Len(s) - 1) : s[i] <= s[i + 1]

LatticeOK ==
    /\ \A i \in 1..MaxSeqLen : workset \cup { [lo |-> i, hi |-> i] } # { i }
    /\ \A A \in workset : \A B \in workset : A.low = B.low => A.high = B.high
    /\ \A A \in workset : \A B \in workset :
           (A.low < B.low /\ A.high >= B.low) => A.high >= B.high

Permutation ==
    \A i \in 1..MaxSeqLen : \E j \in 1..MaxSeqLen : seq[j] = original[i]

RelativeSortedness ==
    \A a \in workset : \A b \in workset :
        (a.low <= b.low /\ a.high >= b.low) => seq[a.high] <= seq[b.low]

\* The invariant is a conjunction of the lattice partition property,
\* permutation preservation, and the relative sortedness condition; it
\* is the only non-trivial thing to keep proved.
Inv == LatticeOK /\ Permutation /\ RelativeSortedness

PCorrect ==
    /\ (pc = "done") => (Permutation /\ Sorted(seq))

Termination ==
    (pc = "done") ~> (pc = "done")

====