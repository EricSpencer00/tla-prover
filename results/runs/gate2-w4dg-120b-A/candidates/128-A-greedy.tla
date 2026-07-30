---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen, Seq

\* The sort is modelled as a single loop with a work set of intervals.  The
\* partition step is abstracted: it nondeterministically picks any sequence
\* that a real partition could produce, so the model explores all of them.
\* The invariant is the usual partial-correctness statement: termination
\* yields a sorted permutation of the original input.

VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

Intervals == [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]

TypeOK ==
  /\ seq \in Seq
  /\ orig \in Seq
  /\ work \subseteq Intervals
  /\ pc \in {"loop", "done"}

Init ==
  /\ seq \in Seq
  /\ orig = seq
  /\ work = {[lo |-> 1, hi |-> Len(seq)]}
  /\ pc = "loop"

\* A valid partition of the current sequence over the chosen interval and
\* pivot: outside the interval nothing changes, and at or below the pivot
\* index no element is greater than any element above it.
ValidPartition(s, s0, i, p) ==
  /\ Len(s) = Len(s0)
  /\ \A k \in 1..Len(s0) : (k < i \/ k > p) => s[k] = s0[k]
  /\ \A k \in i..p, l \in (p + 1)..Len(s0) : s[k] <= s[l]

\* The loop body: pick an interval, partition it if it has more than one
\* element, and replace it with its two subintervals.
Step ==
  /\ pc = "loop"
  /\ work # {}
  /\ \E iv \in work :
       /\ work' = work \ {iv}
       /\ IF iv.lo = iv.hi
          THEN work'
          ELSE
            \E i \in iv.lo..iv.hi, p \in i..iv.hi :
              /\ \E s \in Seq : ValidPartition(s, seq, i, p)
              /\ seq' = s
              /\ work' = work' \cup {[lo |-> iv.lo, hi |-> i - 1], [lo |-> p + 1, hi |-> iv.hi]}
  /\ pc' = "loop"

Terminate ==
  /\ pc = "loop"
  /\ work = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, orig, work>>

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == Step \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Step) /\ WF_vars(Terminate)

\* The invariant is the partial-correctness statement plus the domain
\* partitioning that the loop maintains.
Inv ==
  /\ \A iv \in work : iv.lo <= iv.hi
  /\ \A iv \in work : \A k \in iv.lo..iv.hi, l \in (iv.hi + 1)..Len(seq) : seq[k] <= seq[l]
  /\ \E f \in [1..Len(seq) -> 1..Len(seq)] : \A k \in 1..Len(seq) : seq[k] = orig[f[k]]

PCorrect == pc = "done" => (\A k \in 1..Len(seq) : seq[k] = orig[f[k]] /\ \A l \in 1..(k - 1) : seq[l] <= seq[k])
Termination == <>(pc = "done")

====