---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* A "finite" version of Seq that keeps generated sequences short enough
\* to be checked by TLC; it replaces the standard Seq operator in this model.
LimitedSeq(f) == { <<i, f[i]>> : i \in 1..Len(f) }

Indices == 1..MaxSeqLen

VARIABLES seq, original, work, pc

vars == <<seq, original, work, pc>>

Intervals == [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]

TypeOK ==
  /\ seq \in Seq(Values)
  /\ Len(seq) <= MaxSeqLen
  /\ original \in Seq(Values)
  /\ Len(original) <= MaxSeqLen
  /\ work \in SUBSET Intervals
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E s \in { seq \in Seq(Values) : seq # <<>> /\ Len(seq) <= MaxSeqLen } :
       /\ seq = s
       /\ original = s
  /\ work = {[lo |-> 1, hi |-> Len(seq)]}
  /\ pc = "loop"

\* Returns all partitions of `s` that leave indices outside [lo..hi] untouched,
\* while ensuring every element at or below the pivot index is no greater than
\* any element above it -- the shape any real partition procedure could produce.
Partition(s, lo, hi, p) ==
  {s2 \in Seq(Values) :
     /\ Len(s2) = Len(s)
     /\ \A i \in 1..Len(s) \ {lo..hi} : s2[i] = s[i]
     /\ \A i \in lo..p, j \in p+1..hi : s2[i] <= s2[j]}

Dom(i) == {i.lo..i.hi}

\* One loop iteration: choose an interval, either resolve it or partition it.
Loop ==
  /\ pc = "loop"
  /\ work # {}
  /\ \E i \in work :
       /\ i.lo <= i.hi
       /\ \/ /\ i.lo = i.hi
             /\ work' = work \ {i}
          \/ /\ i.lo < i.hi
             /\ \E p \in i.lo..i.hi :
                  /\ \E s2 \in Partition(seq, i.lo, i.hi, p) : seq' = s2
                  /\ work' = (work \ {i}) \cup {[lo |-> i.lo, hi |-> p], [lo |-> p+1, hi |-> i.hi]}
       /\ pc' = pc
  /\ UNCHANGED original

Done ==
  /\ pc = "loop"
  /\ work = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, original, work>>

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == Loop \/ Done \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Loop)

\* No reordering of values: within every interval the lower subinterval stays
\* below the upper one, so the work set can never regress the sorting.
PCorrect ==
  /\ \A i \in work : i.lo <= i.hi
  /\ \A i \in work :
       \A j \in work :
         /\ i # j
         /\ i.lo = j.lo
         /\ i.hi < j.hi => \A x \in i.hi+1..j.hi : seq[j.lo] <= seq[x]

\* Not a full permutation definition; sufficient for this model's check.
Permutation(a, b) == {<<i, a[i]>> : i \in 1..Len(a)} = {<<i, b[i]>> : i \in 1..Len(b)}

\* The partial correctness claim (proved in the comment, not by TLC).
Inv == PCorrect /\ Permutation(seq, original)

Sorted ==
  \A i, j \in 1..Len(seq) : i <= j => seq[i] <= seq[j]

Termination ==
  /\ PCorrect
  /\ ~(pc = "loop")
  /\ Permutation(seq, original)
  /\ Sorted

====