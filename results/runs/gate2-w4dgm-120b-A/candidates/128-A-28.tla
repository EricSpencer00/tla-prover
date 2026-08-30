---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* domain: the positions of the current sequence, for use in the interval work set
Domain == 1..Len(seq)

Interval == [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]

\* permutes a sequence, used to define the permutation relation on sequences
Permutations == { f \in [Domain -> Domain] :
  (f \in [1..Len(seq1) -> 1..Len(seq1)] /\ \A i \in Domain : f[i] \in 1..Len(seq1)
  /\ \A i, j \in 1..Len(seq1) : (f[i] = f[j]) => (i = j) }

VARIABLES seq, origSeq, workSet, pc

vars == <<seq, origSeq, workSet, pc>>

TypeOK ==
  /\ seq \in [1..MaxSeqLen -> Values \cup {-1}]
  /\ origSeq \in [1..MaxSeqLen -> Values \cup {-1}]
  /\ workSet \subseteq Interval
  /\ pc \in {"main", "done"}

Init ==
  /\ \E s \in (Values \cup {-1})^MaxSeqLen :
       /\ (\E i \in 1..MaxSeqLen : s[i] # -1)
       /\ seq = s
       /\ origSeq = s
  /\ workSet = {[lo |-> 1, hi |-> MaxSeqLen]}
  /\ pc = "main"

\* the one step of the Quicksort loop: partition or finish a singleton interval
MainStep ==
  /\ pc = "main"
  /\ \E int \in workSet :
       \/ int.lo = int.hi
          /\ workSet' = workSet \ {int}
       \/ \E pivot \in int.lo..int.hi :
          /\ \E newseq \in Permutations :
               /\ \A i \in Domain :
                    (int.lo <= i <= int.hi /\ i <= pivot => seq[i] <= newseq[i])
               /\ \A i \in Domain :
                    (int.lo <= i <= int.hi /\ i > pivot => seq[i] >= newseq[i])
               /\ \A i \in Domain : (i < int.lo \/ i > int.hi) => seq[i] = newseq[i]
               /\ seq' = newseq
          /\ workSet' = (workSet \ {int})
                \cup {[lo |-> int.lo, hi |-> pivot], [lo |-> pivot + 1, hi |-> int.hi]}
  /\ pc' = pc

Done ==
  /\ pc = "main"
  /\ workSet = {}
  /\ pc' = "done"
  /\ seq' = seq
  /\ origSeq' = origSeq
  /\ workSet' = workSet

Stall ==
  /\ pc = "done"
  /\ seq' = seq
  /\ origSeq' = origSeq
  /\ workSet' = workSet
  /\ pc' = pc

Next == MainStep \/ Done \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(MainStep) /\ WF_vars(Done)

\* Correctness: a terminated run has produced a sorted permutation of the input
PCorrect ==
  (pc = "done") =>
    /\ \E f \in Permutations : seq = [i \in Domain |-> origSeq[f[i]]]
    /\ \A i \in 1..(Len(seq) - 1) : seq[i] <= seq[i + 1]

\* The partition operator is exactly the nondeterministic choice the model makes,
\* packaged as a derived operator so the .cfg can replace its name with a finite one
LimitedSeq == seq

\* Inductive invariant tying the interval set to the sortedness guarantee
Inv ==
  /\ \A int \in workSet : int.lo <= int.hi
  /\ \A i, j \in Domain :
       (\A int \in workSet : (i \in int.lo..int.hi) => (j \notin int.lo..int.hi))
         => seq[i] <= seq[j]
  /\ \A i \in Domain \ Len(seq) : seq[i] = -1
  /\ \A i \in Domain : seq[i] = -1 => (i = Len(seq) + 1 \/ seq[i + 1] = -1)

TypeOKOK == TypeOK

Termination == <>(pc = "done")

====