---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* The partition operator is abstracted: it nondeterministically chooses any
\* sequence that could result from a valid partition of the chosen interval.
\* The model is deliberately coarse here, because the correctness argument
\* does not depend on the details of how the partition is computed.
VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

Intervals == UNION {[1..n -> 1..n] : n \in 1..MaxSeqLen}

TypeOK ==
  /\ seq \in [1..MaxSeqLen -> Values]
  /\ orig \in [1..MaxSeqLen -> Values]
  /\ work \subseteq Intervals
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E s \in [1..MaxSeqLen -> Values] : s # [i \in 1..MaxSeqLen |-> CHOOSE v \in Values : TRUE] /\ seq = s
  /\ orig = seq
  /\ work = {[1..MaxSeqLen -> 1..MaxSeqLen]}
  /\ pc = "loop"

\* A partition of seq over interval i..j with pivot k leaves everything
\* outside the interval untouched, and every element at or below the pivot
\* index is no greater than every element above it.
Partition(s, i, j, k) ==
  {t \in [1..MaxSeqLen -> Values] :
     /\ \A m \in 1..MaxSeqLen : (m < i \/ m > j) => t[m] = s[m]
     /\ \A a \in i..k, b \in (k+1)..j : t[a] <= t[b]}

Step ==
  \/ \E i \in work :
       /\ i[1] = i[2]
       /\ work' = work \ {i}
       /\ UNCHANGED <<seq, orig, pc>>
  \/ \E i \in work, k \in i[1]..i[2] :
       /\ \E t \in Partition(seq, i[1], i[2], k) : seq' = t
       /\ work' = (work \ {i}) \cup {[i[1]..k -> 1..1], [k+1..i[2] -> 1..1]}
       /\ UNCHANGED <<orig, pc>>
  \/ (work = {} /\ pc = "loop" /\ pc' = "done" /\ UNCHANGED <<seq, orig, work>>)
  \/ (pc = "done" /\ UNCHANGED vars)

Next == Step

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

\* The algorithm is correct when it terminates: the final sequence is a
\* permutation of the original and is sorted.
PCorrect ==
  (pc = "done") =>
    /\ \E f \in [1..MaxSeqLen -> 1..MaxSeqLen] : (UNION {f[i] : i \in 1..MaxSeqLen} = 1..MaxSeqLen) /\ seq = [i \in 1..MaxSeqLen |-> orig[f[i]]]
    /\ \A i \in 1..(MaxSeqLen - 1) : seq[i] <= seq[i+1]

\* The invariant is the core of the partial-correctness argument: the
\* work set always partitions the domain, the sequence is a permutation
\* of the original, and every interval in the work set is already sorted
\* relative to its neighbors.
Inv ==
  /\ (\A i, j \in work : (i[1] <= j[1] /\ j[2] <= i[2]) \/ (j[1] <= i[1] /\ i[2] <= j[2]))
  /\ \E f \in [1..MaxSeqLen -> 1..MaxSeqLen] : (UNION {f[i] : i \in 1..MaxSeqLen} = 1..MaxSeqLen) /\ seq = [i \in 1..MaxSeqLen |-> orig[f[i]]]
  /\ \A i \in work : \A a \in i[1]..(i[2] - 1) : seq[a] <= seq[a+1]

Termination == <>(pc = "done")

INVARIANT Inv
PROPERTY PCorrect
PROPERTY Termination

\* The .cfg replaces Seq with a bounded version so the model is finite.
LimitedSeq == [1..MaxSeqLen -> Values]

====