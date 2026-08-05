---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* Core sorting state: the sequence and a copy of the original for the final
\* permutation check, the set of intervals still to process, and the pc.
VARIABLES seq, original, work, pc

vars == <<seq, original, work, pc>>

Intervals == UNION { [1..n -> 1..n] : n \in 1..MaxSeqLen }

\* The partition operator provides all outcomes that any valid partition
\* routine could produce on the chosen interval and pivot.
VARIABLE Partition
RECURSIVE Perm(_)
Perm(s) == IF s = <<>> THEN {<<>>}
           ELSE { y << e : y \in Perm(tail(s)) : e \in Values }

VARIABLE Permute
Permute == { g \in [1..MaxSeqLen -> Values] : \A i \in 1..MaxSeqLen : g[i] \in Values }

\* A finite, checkable version of Sequences.Seq; the .cfg swaps it in.
LimitedSeq(S) == { s \in [1..Len(S) -> S] : \A i \in 1..Len(S) : s[i] \in S }

TypeOK ==
  /\ seq \in Permute
  /\ original \in Permute
  /\ work \in SUBSET Intervals
  /\ pc \in {"main", "done"}

Init ==
  /\ \E s \in LimitedSeq(Values) : seq = s /\ original = s
  /\ work = {[1 ||-> 1, Len(seq) ||-> Len(seq)]}
  /\ pc = "main"

\* One iteration: pick an interval and either discard a singleton or
\* split it around a pivot, nondeterministically choosing a partition
\* consistent with the pivot ordering.
PartitionStep ==
  /\ pc = "main"
  /\ \E i \in work :
       LET lo == i[1] IN LET hi == i[Len(i)] IN
       LET sub == { z \in work : z # i } IN
         IF lo = hi
         THEN /\ work' = sub
         ELSE
           \E x \in lo..hi :
             /\ LET loInt == [1 ||-> lo, Len(i) - 1 ||-> x] IN
                LET hiInt == [1 ||-> x + 1, Len(i) - 1 ||-> hi] IN
                /\ work' = sub \cup {loInt, hiInt}
                /\ \E s \in Partition([seq, lo, x, hi]) : seq' = s
         /\ original' = original
         /\ pc' = "main"

Stall == pc = "done" /\ pc' = "done" /\ UNCHANGED vars

Next == PartitionStep \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(PartitionStep)

PCorrect ==
  pc = "done" => /\ Perm(seq) \subseteq Perm(original) /\ \A i \in 1..(Len(seq) - 1) : seq[i] <= seq[i + 1]

\* The invariant is the structured partial-correctness argument: the work
\* set forms a domain partition, the sequence is always a permutation of
\* the original, and every interval that has been processed is sorted.
Inv ==
  /\ (UNION work) = (1..Len(seq))
  /\ \A i, j \in work : (i # j) => (Domain(i) \cap Domain(j) = {})
  /\ Perm(seq) \subseteq Perm(original)
  /\ \A i \in work : \A a, b \in i : a < b => seq[a] <= seq[b]

Termination == <>(pc = "done")

====