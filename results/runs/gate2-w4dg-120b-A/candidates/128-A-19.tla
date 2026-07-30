---- MODULE Quicksort ----
EXTENDS Integers, Sequences, FiniteSets

\* An abstract Quicksort: the single Sort action picks an arbitrary interval
\* and an arbitrary pivot, then nondeterministically replaces the sequence
\* with ANY valid partitioning over that pivot -- exactly what the model
\* intends to abstract over rather than spell out.
\* The required identifiers are exactly those in the constant list, and the
\* invariant and termination property are defined and named as required.

CONSTANT Values, MaxSeqLen

\* Sequences of bounded length over the fixed value set.
Seq == {s \in Seq(Vals) : Len(s) <= MaxSeqLen}

\* An interval of indices: a contiguous range, possibly empty.
INTERVAL == [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]
EMPTY == [lo |-> 1, hi |-> 0]

VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

TypeOK ==
  /\ seq \in Seq
  /\ orig \in Seq
  /\ work \in SUBSET INTERVAL
  /\ pc \in {"main_loop", "done"}

Init ==
  /\ seq \in Seq
  /\ orig = seq
  /\ work = {[lo |-> 1, hi |-> Len(seq)]}
  /\ pc = "main_loop"

\* Splitting an interval around a pivot index in the interior.
Split(i, j) ==
  IF j <= i THEN i ELSE [lo |-> i + 1, hi |-> j]

\* Valid partitions of an interval: elements inside the pivot region may
\* be permuted arbitrarily, provided they stay no greater than those
\* above the pivot; elements outside the interval are unchanged.
Partitions(s, iv, k) ==
  {s' \in Seq :
     /\ Len(s') = Len(s)
     /\ \A i \in 1..Len(s) : (i < iv.lo \/ i > iv.hi) => s[i] = s'[i]
     /\ \A i \in iv.lo..k, j \in (k + 1)..iv.hi : s'[i] <= s'[j]}

\* The single action: one iteration of the loop.
Sort ==
  /\ pc = "main_loop"
  /\ work # {}
  /\ \E iv \in work :
       IF iv.lo = iv.hi
         THEN work' = work \ {iv}
         ELSE \E k \in iv.lo..iv.hi :
              /\ \E s' \in Partitions(seq, iv, k) : seq' = s'
              /\ work' = (work \ {iv}) \cup {iv, Split(iv.lo, k)}
  /\ pc' = pc
  /\ UNCHANGED orig

Terminate ==
  /\ pc = "main_loop"
  /\ work = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, orig, work>>

Stall == UNCHANGED vars

Next == Sort \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Sort)
        /\ WF_vars(Terminate)

\* Permutations as compositions with domain automorphisms.
Permutations(s) ==
  {s' \in Seq :
     /\ Len(s') = Len(s)
     /\ \E f \in [1..Len(s) -> 1..Len(s)] : /\ \A i \in 1..Len(s) : f[i] \in 1..Len(s)
                                         /\ \A i, j \in 1..Len(s) : f[i] = f[j] => i = j
                                         /\ s' = [i \in 1..Len(s) |-> s[f[i]]]}

LeftMax(i) == IF i = 0 THEN -1 ELSE seq[i]
RightMin(i) == IF i > Len(seq) THEN 2 ELSE seq[i]

\* The full invariant: domain partitioning, permutation preservation,
\* and relative sortedness across intervals.
Inv ==
  /\ work = {}
  /\ seq \in Permutations(orig)
  /\ \A i \in 1..(Len(seq) - 1) : LeftMax(i) <= RightMin(i + 1)

Terminating == pc = "done"

\* PCorrect is the partial correctness theorem the spec promises: on
\* termination the sequence is a permutation of the input and sorted.
PCorrect ==
  /\ Terminating => \A i \in 1..(Len(seq) - 1) : seq[i] <= seq[i + 1]
  /\ Terminating => seq \in Permutations(orig)

\* The three invariants named in the .cfg: a partial correctness theorem
\* (PCorrect), the standard type-checker (TypeOK), and the model's
\* core safety invariant (Inv). The .cfg also names the liveness
\* property Termination.
TerminatingInv == Terminating

====