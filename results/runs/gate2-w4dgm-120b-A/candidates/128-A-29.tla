---- MODULE Quicksort ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* Order-preserving partition of the interval around a pivot index.
RECURSIVE SortedUntil(_, _)
SortedUntil(seq, i) ==
  IF i = 0 THEN {}
  ELSE {seq[i]} \cup SortedUntil(seq, i - 1)

VARIABLES seq, orig, todo, pc

vars == <<seq, orig, todo, pc>>

Intervals == [lo: 1 .. MaxSeqLen, hi: 1 .. MaxSeqLen]

TypeOK ==
  /\ seq \in Seq(Values)
  /\ orig \in Seq(Values)
  /\ todo \subseteq Intervals
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E s \in Seq(Values) : Len(s) >= 1 /\ s # << >> /\ seq = s /\ orig = s
  /\ todo = {[lo |-> 1, hi |-> Len(seq]]}
  /\ pc = "loop"

\* The partition operator abstracts a real partition procedure:
\* it keeps every element outside [i..j] the same and
\* rearranges the interval so the split point has the required
\* ordering property.
Permuter(i, j, k) ==
  { w \in Seq(Values) :
      /\ Len(w) = Len(seq)
      /\ \A x \in 1 .. Len(seq) : x < i \/ x > j => w[x] = seq[x]
      /\ \A x \in i .. k : \A y \in (k + 1) .. j : w[x] <= w[y] }

\* One loop iteration: pick an interval, partition it if needed,
\* and replace it by its two subintervals.
PartitionStep ==
  /\ pc = "loop"
  /\ \E r \in todo :
       /\ LET i == r.lo
            j == r.hi
       IN IF i = j
          THEN /\ todo' = (todo \ {r})
               /\ seq' = seq
          ELSE /\ \E k \in i .. (j - 1) :
                 /\ \E w \in Permuter(i, j, k) : seq' = w
                 /\ todo' = (todo \ {r}) \cup {[lo |-> i, hi |-> k], [lo |-> k + 1, hi |-> j]}
          /\ UNCHANGED orig
  /\ pc' = IF todo = {} THEN "done" ELSE "loop"

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == PartitionStep \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(PartitionStep)

PCorrect ==
  (pc = "done") => /\ \A x \in Intervals : x \notin todo => x.hi <= x.lo
                  /\ seq \in Permutations(orig)

\* The sorted-and-permuted invariant: it is restricted to the indices
\* that lie inside at least one of the two subintervals of the first split.
RelSorted ==
  \E k \in 1 .. Len(seq) :
    \E x \in Intervals, y \in Intervals :
      /\ x.hi <= k
      /\ k + 1 <= y.lo
      /\ \A i \in 1 .. k : \A j \in (k + 1) .. Len(seq) : seq[i] <= seq[j]

Inv == RelSorted /\ PCorrect

Termination == <>(pc = "done")

\* The model's sequence operator is capped at MaxSeqLen so the state space is finite.
LimitedSeq(n) == IF n <= MaxSeqLen THEN Seq(n) ELSE Seq(MaxSeqLen)
====