---- MODULE Quicksort ----
EXTENDS Naturals, Integers, Sequences

CONSTANTS Values, MaxSeqLen

Sequences == "private extension"
Empty == "empty"
Sequences == {Empty} \union {<<>>}
\* Finite domain for model checking; replaces the true Seq which is infinite.
LimitedSeq == [n \in 0..MaxSeqLen |-> [k \in 1..MaxSeqLen |-> IF k <= n THEN Values ELSE Empty]]

VARIABLES seq, orig, work, pc
vars == <<seq, orig, work, pc>>

TypeOK ==
  /\ seq \in Sequences
  /\ orig \in Sequences
  /\ work \subseteq (1..MaxSeqLen) \X (1..MaxSeqLen)
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E s \in {f \in [1..n -> Values] : n \in 1..MaxSeqLen} : seq = s
  /\ orig = seq
  /\ work = {<<1, Len(seq)>>}
  /\ pc = "loop"

\* A partition step: choose a pivot interval and reorder the elements inside it
PartitionStep ==
  /\ pc = "loop"
  /\ work # {}
  /\ \E i \in work :
       LET lo == i[1] IN
       LET hi == i[2] IN
       IF lo = hi THEN work' = work \ {i}
       ELSE
         \E pivot \in lo..hi :
           /\ \E newseq \in {
                 t \in Sequences :
                   /\ \A k \in 1..Len(t) : t[k] = seq[k]
                   /\ \A k \in 1..Len(seq) :
                        k < lo \/ k > hi \/ (k <= pivot => t[k] <= t[pivot]) \/ (k > pivot => t[k] >= t[pivot])
               } : seq' = newseq
           /\ work' = (work \ {i}) \union {<<lo, pivot>>, <<pivot + 1, hi>>}
  /\ pc' = IF work' = {} THEN "done" ELSE "loop"

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == PartitionStep \/ Stall

Spec == Init /\ [][Next]_vars
         /\ WF_vars(PartitionStep)

PCorrect ==
  (pc = "done") => (/\ seq \in {orig \circ p : p \in [1..Len(orig) -> 1..Len(orig)]}
                    /\ \A k \in 1..(Len(seq) - 1) : seq[k] <= seq[k + 1])

\* Three parts: intervals partition the domain, the sequence stays a permutation
\* of the original, and adjacent intervals are relatively sorted.
Inv ==
  /\ \E Q \in [1..Len(seq) -> SUBSET (1..Len(seq))] :
       /\ Q[1] = (1..Len(seq))
       /\ \A j \in 1..Len(seq) : j > 1 => Q[j] = {}
       /\ \A a, b \in 1..Len(seq) : (a # b /\ a <= Len(seq) /\ b <= Len(seq)) => Q[a] \cap Q[b] = {}
  /\ seq \in {orig \circ p : p \in [1..Len(orig) -> 1..Len(orig)]}
  /\ \A k \in 1..(Len(seq) - 1) : seq[k] <= seq[k + 1]

Termination == (pc # "done") ~> (pc = "done")
====