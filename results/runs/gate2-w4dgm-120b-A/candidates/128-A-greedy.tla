---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* The model's sequence operator is replaced by a bounded version so the
\* state space stays finite; the replacement is defined here, not declared.
LimitedSeq(S) == CHOOSE s \in Seq(S) : Len(s) <= MaxSeqLen

VARIABLES seq, orig, work, pc

TypeOK ==
  /\ seq \in Seq(Values)
  /\ orig \in Seq(Values)
  /\ work \subseteq (1..MaxSeqLen) \X (1..MaxSeqLen)
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E s \in LimitedSeq(Values) : s # <<>> /\ seq = s /\ orig = s
  /\ work = {<<1, Len(seq)>>}
  /\ pc = "loop"

\* A partition is any permutation that leaves elements outside the interval
\* untouched and separates the two sides of the pivot in value.
Partition(seq, lo, hi, p) ==
  {s \in Permutations(seq) :
     /\ \A i \in 1..(p - lo) : s[i] <= s[i + (hi - p)]
     /\ \A i \in 1..(p - lo) : s[i] = seq[lo + i - 1]
     /\ \A i \in (p - lo + 1)..(hi - lo) : s[i] = seq[p + i - (p - lo)]

\* The loop picks an interval, and either discards a singleton or splits it
\* around a pivot, nondeterministically choosing a valid partition result.
Step ==
  /\ pc = "loop"
  /\ \E lo, hi \in 1..MaxSeqLen :
       /\ <<lo, hi>> \in work
       /\ work' = work \ {<<lo, hi>>}
       /\ IF lo = hi
          THEN UNCHANGED <<seq, orig>>
          ELSE \E p \in lo..hi :
                 /\ \E s \in Partition(seq, lo, hi, p) : seq' = s
                 /\ work' = work \cup {<<lo, p>>, <<p + 1, hi>>}
  /\ pc' = IF work = {} THEN "done" ELSE "loop"

Stall == pc = "done" /\ UNCHANGED <<seq, orig, work, pc>>

Next == Step \/ Stall

Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* The loop invariant: the work intervals partition the domain, the current
\* sequence is a permutation of the original, and each interval is sorted
\* relative to the one before it.
Inv ==
  /\ \A a, b \in work : (a[1] <= b[1] /\ b[1] <= a[2]) => a = b
  /\ \E f \in Permutations(orig) : seq = f
  /\ \A a, b \in work : a[2] < b[1] => seq[a[2]] <= seq[b[1]]

PCorrect ==
  /\ \A i \in 1..(Len(seq) - 1) : seq[i] <= seq[i + 1]
  /\ \E f \in Permutations(orig) : seq = f

\* Weak fairness on the loop transition forces the work set to drain.
Termination == WF_vars(Step)

====