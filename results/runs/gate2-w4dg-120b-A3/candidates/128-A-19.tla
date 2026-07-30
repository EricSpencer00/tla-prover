---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

\* The model checks a bounded version of quicksort.  Values is the set of
\* integer values the sequence can hold, and MaxSeqLen caps the length of
\* the sequence for model checking.
CONSTANTS Values, MaxSeqLen

\* Sequences.Seq is unbounded; FiniteSequences.Seq is not.  This
\* definition replaces the unbounded Seq with a bounded version.
\* (The name on the left -- LimitedSeq -- is the one introduced here;
\* Sequences.Seq is imported and never redefined.)
LimitedSeq(S) == CHOOSE f \in [1..Len(S) -> Values] : TRUE

VARIABLES seq, orig, workset, pc
vars == <<seq, orig, workset, pc>>

\* A partitioned interval has a lower part (everything at or below the
\* pivot index) and an upper part (everything above it).  The operator
\* below enumerates every sequence reachable by some partition that
\* respects this ordering -- it is the nondeterministic choice made by
\* the algorithm during a loop iteration.
PartitionsOf(S, lo, hi) ==
  { T \in [1..Len(S) -> Values] :
      /\ \A i \in 1..Len(S) : (i < lo \/ i > hi) => T[i] = S[i]
      /\ \A i \in lo..hi : \A j \in lo..hi :
           (i <= hi /\ j > hi) => T[i] <= T[j] }

Automorphisms == { f \in [1..MaxSeqLen -> 1..MaxSeqLen] :
                     \A i, j \in 1..MaxSeqLen : (i = j) <=> (f[i] = f[j]) }

TypeOK ==
  /\ seq \in [1..MaxSeqLen -> Values]
  /\ orig \in [1..MaxSeqLen -> Values]
  /\ workset \subseteq [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]
  /\ pc \in {"loop", "done"}

Init ==
  /\ seq \in [1..MaxSeqLen -> Values]
  /\ orig = seq
  /\ workset = {[lo |-> 1, hi |-> MaxSeqLen]}
  /\ pc = "loop"

\* Coherent intervals: any two intervals in the work set are either
\* disjoint or one is wholly contained in the other.  This is the
\* partitioning discipline that keeps the loop well-founded.
Coherent ==
  \A a, b \in workset :
    \/ a = b
    \/ a.hi < b.lo
    \/ b.hi < a.lo
    \/ (b.lo <= a.lo /\ a.hi <= b.hi)
    \/ (a.lo <= b.lo /\ b.hi <= a.hi)

PermutationPreserved ==
  \A f \in Automorphisms : seq = [i \in 1..MaxSeqLen |-> orig[f[i]]]

RelativeSortedness ==
  \A a, b \in workset :
    (a.hi < b.lo) => (a.lo <= MaxSeqLen /\ seq[a.hi] <= seq[b.lo])

Inv == Coherent /\ PermutationPreserved /\ RelativeSortedness

\* A loop iteration picks an interval and either drops it (a singleton)
\* or replaces it with two subintervals around a pivot index, moving to
\* a partitioned version of the sequence.
LoopStep ==
  \/ \E r \in workset :
       /\ workset' = workset \ {r}
       /\ pc' = pc
       /\ UNCHANGED <<seq, orig>>
  \/ \E r \in workset, p \in r.lo..r.hi, s \in PartitionsOf(seq, r.lo, r.hi) :
       /\ p \in r.lo..r.hi
       /\ seq' = s
       /\ workset' = (workset \ {r})
                    \cup {[lo |-> r.lo, hi |-> p]}
                    \cup {[lo |-> p + 1, hi |-> r.hi]}
       /\ pc' = pc
       /\ UNCHANGED orig

Terminate ==
  /\ pc = "loop"
  /\ workset = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, orig, workset>>

Stall == pc = "done" /\ UNCHANGED vars

Next == LoopStep \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars
        /\ SF_vars(LoopStep)
        /\ SF_vars(Terminate)

\* Partial correctness: termination implies the result is a sorted
\* permutation of the input.
PCorrect ==
  (pc = "done") =>
    /\ PermutationPreserved
    /\ \A i \in 1..(MaxSeqLen - 1) : seq[i] <= seq[i + 1]

Termination == (pc = "loop") ~> (pc = "done")
====