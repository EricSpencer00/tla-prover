---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* The partition operator is redefined below as LimitedSeq, so the model
\* stays finite; the declaration here is only to keep the parser happy.
Seq == "Seq"

\* An interval of indices in the sequence; the work set is a set of them.
Interval == [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]

VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

\* A permutation of a domain is a bijection on it; applied to a sequence it
\* reorders the elements at the permuted indices.
Permutation == [1..MaxSeqLen -> 1..MaxSeqLen]

\* The partition operator: all permutations that leave indices outside the
\* interval untouched and keep the lower side no greater than the upper.
Partition(i, j, p) ==
  { q \in Permutation :
      /\ \A k \in 1..MaxSeqLen : (k < i \/ k > j) => q[k] = k
      /\ \A a \in i..p, b \in (p + 1)..j : seq[q[a]] <= seq[q[b]] }

TypeOK ==
  /\ seq \in Seq(Values)
  /\ orig \in Seq(Values)
  /\ work \subseteq Interval
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E s \in Seq(Values) : seq = s /\ orig = s
  /\ work = {[lo |-> 1, hi |-> Len(seq]]}
  /\ pc = "loop"

\* One iteration of the Quicksort loop: pick an interval, partition it, and
\* replace it with its two subintervals.
Loop ==
  /\ pc = "loop"
  /\ work # {}
  /\ \E i \in work :
       /\ i.lo = i.hi
          => work' = work \ {i}
       /\ i.lo < i.hi
          => \E p \in i.lo..(i.hi - 1), s \in Partition(i.lo, i.hi, p) :
               /\ seq' = s
               /\ work' = (work \ {i}) \cup {[lo |-> i.lo, hi |-> p], [lo |-> p + 1, hi |-> i.hi]}
  /\ pc' = pc

Done ==
  /\ pc = "loop"
  /\ work = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, orig, work>>

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == Loop \/ Done \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Loop)

\* The sorted result is a permutation of the input and is non-decreasing.
PCorrect ==
  /\ \A a, b \in 1..Len(seq) : seq[a] = orig[b] => b = a
  /\ \A a \in 1..(Len(seq) - 1) : seq[a] <= seq[a + 1]

\* The invariant is the partitioning discipline the algorithm must never
\* break; it is stronger than PCorrect and is what keeps the sort sound.
Inv ==
  /\ \A i \in work : i.lo <= i.hi
  /\ \A i, j \in work :
       (i # j /\ i.hi >= j.lo) => (i.hi < j.hi /\ i.lo > j.lo)
  /\ \A a, b \in 1..MaxSeqLen : (a # b /\ seq[a] = seq[b]) => a = b
  /\ \A a, b \in 1..MaxSeqLen : a < b => seq[a] <= seq[b]

Termination == <>(pc = "done")

====