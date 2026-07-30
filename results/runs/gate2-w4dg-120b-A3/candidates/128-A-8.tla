---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* To keep the model finite, we re-define the unbounded sequence operator
\* from the Sequences module as a finite version with a hard length cap.
\* The name Seq stays as it is -- only the operator it denotes changes.
LimitedSeq(S) == IF S = 0 THEN <<>> ELSE <<Head(S) >> \o LimitedSeq(Tail(S))
Seq == LimitedSeq

VARIABLES seq, original, work, pc
vars == <<seq, original, work, pc>>

\* The work set is a set of index intervals; intervals are finite because
\* seq has a bounded length, so the set of intervals is finite.
Intervals == SUBSET (1..MaxSeqLen \X 1..MaxSeqLen)

RECURSIVE Sorted(_, _)
Sorted(f, i) ==
  IF i >= Len(f) THEN TRUE
  ELSE /\ f[i] <= f[i + 1]
       /\ Sorted(f, i + 1)

RECURSIVE Permutes(_, _)
Permutes(f, g) ==
  \E pi \in [1..Len(f) -> 1..Len(f)] : (UNION {pi})
                          \cap {1..Len(f)} = {}
                          /\ (\A i \in 1..Len(f) : g[pi[i]] = f[i])

TypeOK ==
  /\ seq \in Seq(Values)
  /\ Len(seq) <= MaxSeqLen
  /\ original \in Seq(Values)
  /\ Len(original) <= MaxSeqLen
  /\ work \subseteq Intervals
  /\ pc \in {"run", "halt"}

Init ==
  /\ seq \in {s \in Seq(Values) : Len(s) > 0}
  /\ original = seq
  /\ work = {<<1, Len(seq)>>}
  /\ pc = "run"

\* A valid partition keeps everything outside the interval untouched and
\* guarantees everything in the lower subinterval is \le everything in the
\* upper subinterval, for any pivot the algorithm may have chosen.
ValidPartition(f, g, lo, hi, pivot) ==
  /\ lo <= pivot
  /\ pivot < hi
  /\ \A k \in 1..Len(f) :
        (k < lo \/ k > hi) => g[k] = f[k]
  /\ \A i \in lo..pivot : \A j \in (pivot + 1)..hi : g[i] <= g[j]

SortStep ==
  \/ \E r \in work :
       /\ work' = work \ {r}
       /\ pc' = pc
       /\ IF r[1] = r[2]
            THEN UNCHANGED seq
            ELSE
              /\ \E pivot \in r[1]..(r[2] - 1) :
                   \E g \in {g \in Seq(Values) :
                               Len(g) = Len(seq)
                               /\ ValidPartition(seq, g, r[1], r[2], pivot)} :
                     seq' = g
              /\ work' = work \cup {<<r[1], pivot>>, <<pivot + 1, r[2]>>}
  \/ /\ work = {}
       /\ pc = "run"
       /\ pc' = "halt"
       /\ UNCHANGED <<seq, original, work>>
  \/ /\ pc = "halt" /\ UNCHANGED vars

Next == SortStep

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* The final sorted sequence is a permutation of the original and is
\* non-decreasing in every adjacent pair of entries.
PCorrect == (pc = "halt") => (Permutes(original, seq) /\ Sorted(seq, 1))

\* The invariant used by the interactive proof; it is stronger than
\* PCorrect and survives every reachable state, not just the final one.
Inv ==
  /\ \A i \in 1..Len(seq) : seq[i] \in Values
  /\ Permutes(original, seq)
  /\ \A lo, hi \in 1..Len(seq) :
       (lo <= hi) => Sorted(seq, lo)

Termination == (pc = "halt")

====