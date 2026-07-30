---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen, Seq

\* The sorting work set holds contiguous intervals of the sequence.  A
\* partition step is modeled as an arbitrary nondeterministic replacement
\* of the sequence on the chosen interval that satisfies the pivot
\* ordering; it is NOT a faithful copy of the real Quicksort partition.
\* This is intentional, because the spec only has to prove that any
\* sequence reachable from such a step is still a sorted permutation.

VARIABLES seq, original, work, pc

vars == << seq, original, work, pc >>

Intervals == [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]
PivotPositions == 1..(MaxSeqLen - 1)
Thread == [state: {"main", "done"}]
NonEmpty == {s \in Seq : Len(s) > 0}

TypeOK ==
  /\ seq \in NonEmpty
  /\ original \in NonEmpty
  /\ work \subseteq Intervals
  /\ pc \in Thread

Init ==
  /\ \E s \in NonEmpty : seq = s /\ original = s
  /\ work = {[lo |-> 1, hi |-> Len(seq)]}
  /\ pc.state = "main"

\* Partition is the set of all possible results of a partition step on the
\* chosen interval: the subsequence outside the interval is untouched, and
\* everything left of the pivot index is no greater than everything right
\* of it.  This is a pure existence predicate, not a deterministic rule.
Partition(S, interval, p) ==
  { T \in NonEmpty :
      /\ \A i \in 1..Len(S) : (i < interval.lo \/ i > interval.hi) => T[i] = S[i]
      /\ \A i \in interval.lo..p, j \in (p + 1)..interval.hi : T[i] <= T[j]
  }

\* The one action of the state machine: pick an interval, split it if it
\* is longer than one, and replace the original interval in the work set
\* with its two halves.  The sequence is replaced by any partition that
\* satisfies the pivot ordering.
Iterate ==
  /\ pc.state = "main"
  /\ \E interval \in work :
       /\ work' = work \ {interval}
       /\ (IF interval.lo = interval.hi
            THEN work'
            ELSE
              \E p \in PivotPositions :
                /\ p >= interval.lo /\ p < interval.hi
                /\ LET lower  == [lo |-> interval.lo, hi |-> p]
                       upper  == [lo |-> p + 1, hi |-> interval.hi]
                       parts == Partition(seq, interval, p)
                   IN \E T \in parts :
                        /\ seq' = T
                        /\ work' = work' \cup {lower, upper})
       /\ pc' = [state |-> "main"])
  /\ UNCHANGED original

Terminate ==
  /\ pc.state = "main"
  /\ work = {}
  /\ pc' = [state |-> "done"]
  /\ UNCHANGED << seq, original, work >>

Stall ==
  /\ pc.state = "done"
  /\ UNCHANGED vars

Next == Iterate \/ Terminate \/ Stall

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Iterate)
  /\ WF_vars(Terminate)

\* The sortedness invariant is the nontrivial part: every position to the
\* left of an interval boundary is no greater than the position at the
\* boundary, and every boundary is no greater than the position to its
\* right.  Together with permutation preservation this is what forces
\* the sequence to be sorted once the work set has emptied.
Inv ==
  /\ \A interval \in work : interval.lo <= interval.hi
  /\ \A i \in 1..(MaxSeqLen - 1) : seq[i] <= seq[i + 1]
  /\ Permutation(original, seq)

PCorrect == pc.state = "done" => (\A i \in 1..(Len(seq) - 1) : seq[i] <= seq[i + 1])
Termination == <>(pc.state = "done")

====