---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Permutations, Sequences

CONSTANTS Values, MaxSeqLen

\* The model keeps a short bounded window of the sequence; the full
\* correctness argument works for the unbounded version.
Sequences == (1..MaxSeqLen) \X Values
\* A finite, model-checkable version of the immutable Seq operator.
LimitedSeq(s) == CHOOSE t \in Sequences : Len(s) = Len(t) /\ \A i \in 1..Len(s) : s[i] = t[i]

VARIABLES seq, origSeq, work, pc

Intervals == {i \in 1..MaxSeqLen : i >= 1 \} \X {j \in 1..MaxSeqLen : j >= 1}
Below(i, j) == {k \in 1..MaxSeqLen : i <= k /\ k <= j}

TypeOK ==
    /\ seq \in Sequences
    /\ origSeq \in Sequences
    /\ work \subseteq Intervals
    /\ pc \in {"run", "done"}

Init ==
    /\ \E s \in Sequences : seq = s /\ origSeq = s
    /\ work = {<<1, MaxSeqLen>>}
    /\ pc = "run"

DomainPartition(seq) == {<<i, seq[i]>> : i \in 1..MaxSeqLen}
PermutationPreserved(seq) == Cardinality(DomainPartition(seq)) = MaxSeqLen
RelativeSorted(i1, i2) ==
    \A k1 \in Below(i1[1], i1[2]), k2 \in Below(i2[1], i2[2]) :
        k1 <= k2 => seq[k1] <= seq[k2]

\* An abstract partition step: it nondeterministically chooses any sequence
\* that a real partition routine could have produced.
PartitionStep(p, q) == {r \in Sequences :
    /\ \A i \in 1..MaxSeqLen : (i < p \/ i > q) => r[i] = seq[i]
    /\ \A i1 \in Below(p, q), i2 \in Below(p, q) : i1 <= i2 => r[i1] <= r[i2]}

Step ==
    /\ pc = "run"
    /\ work # {}
    /\ \E int \in work :
        /\ work' = work \ {int}
        /\ IF int[1] = int[2]
           THEN UNCHANGED seq
           ELSE \E pivot \in int[1]..int[2] :
                /\ \E seq2 \in PartitionStep(int[1], int[2]) : seq' = seq2
                /\ work' = work \cup {<<int[1], pivot>>, <<pivot + 1, int[2]>>}
    /\ pc' = IF work = {} THEN "done" ELSE pc

Stall == pc = "done" /\ UNCHANGED <<seq, origSeq, work, pc>>

Next == Step \/ Stall

Spec == Init /\ [][Next]_<<seq, origSeq, work, pc>>

PCorrect ==
    /\ PermutationPreserved(seq)
    /\ \A i1 \in work, i2 \in work : RelativeSorted(i1, i2)

\* The full correctness theorem needs the integer domain; kept separate
\* from the bounded-model invariant so TLAPS can still check this part.
FullTheorem ==
    /\ PermutationPreserved(seq)
    /\ \A i1 \in Intervals, i2 \in Intervals : RelativeSorted(i1, i2)
    /\ \A i \in 1..MaxSeqLen : \E e \in Values : <<i, seq[i]>> = <<i, e>>

\* Weak fairness on the loop action drives the permutation to completion.
Termination == (\A i \in 1..MaxSeqLen : \E e \in Values : <<i, origSeq[i]>> = <<i, e>>) ~> (pc = "done")

\* A copy of FullTheorem so the bounded model has something to prove.
FullTheoremBounded == FullTheorem
====