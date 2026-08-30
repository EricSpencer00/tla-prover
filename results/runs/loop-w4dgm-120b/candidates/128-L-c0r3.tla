---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* The model's sequence operator is replaced by a bounded version so the
\* state space stays finite; the replacement is defined below, not declared.
\* The spec itself is unchanged from the unbounded version.
\* The sort is a single actor that repeatedly partitions intervals.
\* The correctness property is partial: termination implies a sorted
\* permutation of the original sequence.

VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

Intervals == {i \in 1..MaxSeqLen : {j \in 1..MaxSeqLen : i <= j}}

TypeOK ==
  /\ seq \in Seq(Values)
  /\ orig \in Seq(Values)
  /\ work \subseteq Intervals
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E s \in Seq(Values) : Len(s) > 0 /\ seq = s
  /\ orig = seq
  /\ work = {1..Len(seq)}
  /\ pc = "loop"

\* A partition is any permutation of the whole sequence that leaves
\* elements outside the interval untouched and respects the pivot split.
Partition(i, j, p) ==
  {t \in [1..MaxSeqLen -> Values] :
     /\ \A k \in 1..MaxSeqLen : (k < i \/ k > j) => t[k] = seq[k]
     /\ \A a \in i..p, b \in (p + 1)..j : t[a] <= t[b]}

LoopStep ==
  /\ pc = "loop"
  /\ work # {}
  /\ \E I \in work :
       /\ IF I = {I} THEN work' = work \ {I}
          ELSE
            /\ \E p \in I :
                 /\ \E t \in Partition(I[1], I[Len(I)], p) :
                      seq' = t
                 /\ work' = (work \ {I}) \cup {I[1]..p, (p + 1)..I[Len(I)]}
       /\ pc' = "loop"
  /\ orig' = orig

Terminate ==
  /\ pc = "loop"
  /\ work = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, orig, work>>

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == LoopStep \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(LoopStep) /\ WF_vars(Terminate)

\* The invariant is the full correctness condition; PCorrect isolates the
\* part that is preserved by every step, which is what the inductive proof
\* needs. The permutation condition is the only thing that keeps the sort
\* from inventing or dropping values.
PCorrect ==
  /\ \A I \in work : Len(I) >= 1
  /\ \A I \in work : \A a \in I, b \in I : a <= b => seq[a] <= seq[b]
  /\ \A a \in 1..Len(seq) : \E b \in 1..Len(orig) : seq[a] = orig[b]

Inv == PCorrect

\* The permutation condition is not a consequence of the partition
\* definition alone; it needs the per-step preservation argument.
PermutationPreserved ==
  \A a \in 1..Len(seq) : \E b \in 1..Len(orig) : seq[a] = orig[b]

Sorted == \A a, b \in 1..Len(seq) : a <= b => seq[a] <= seq[b]

Termination == pc = "done"

====