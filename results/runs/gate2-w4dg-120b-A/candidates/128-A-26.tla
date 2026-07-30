---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen, Seq

\* The full, detailed state: the current sequence, the original input (for the
\* permutation check), the work set of intervals, and a pc that is either the
\* loop label or the terminal label.
VARIABLES a, orig, work, pc
vars == <<a, orig, work, pc>>

\* Intervals are inclusive index ranges, and are always ordered low <= high.
Interval == [low: 1..MaxSeqLen, high: 1..MaxSeqLen]
NoWork == [low |-> 1, high |-> 0]
Domain == 1..Len(a)

\* The partition operator: a full set of possible outcomes once a pivot and an
\* index k have been chosen, so the machine can nondeterministically pick any
\* valid partition without having to model the pointer dance.
Partition(i, k) ==
  { x \in [Domain -> Values] :
      /\ \A m \in Domain :
           (m <= k /\ i.low <= m /\ m <= i.high) =>
             x[m] <= x[k]
      /\ \A m \in Domain :
           (m > k /\ i.low <= m /\ m <= i.high) => x[k] <= x[m]
      /\ \A m \in Domain : (m < i.low \/ m > i.high) => x[m] = a[m] }

\* Two intervals are adjacent when they sit side by side with no gap between.
Adjacent(i, j) ==
  (i.high + 1 = j.low /\ i.low <= i.high /\ j.low <= j.high)
  \/ (j.high + 1 = i.low /\ j.low <= j.high /\ i.low <= i.high)

TypeOK ==
  /\ a \in [Domain -> Values]
  /\ orig \in [Domain -> Values]
  /\ work \subseteq Interval
  /\ pc \in {"Loop", "Done"}

Init ==
  /\ a = Seq
  /\ orig = Seq
  /\ work = {[low |-> 1, high |-> Len(Seq)]}
  /\ pc = "Loop"

\* The full sorting-step, which folds the partition choice into one atomic
\* nondeterministic choice of the next sequence, indexed by the pivot.
Step ==
  /\ pc = "Loop"
  /\ work # {}
  /\ \E i \in work :
       /\ work' = work \ {i}
       /\ IF i.low = i.high
          THEN work'
          ELSE
            /\ \E k \in i.low..i.high :
                 /\ k \in Domain
                 /\ \E x \in Partition(i, k) :
                      /\ a' = x
                      /\ work' = work' \cup
                         {[low |-> i.low, high |-> k], [low |-> k + 1, high |-> i.high]}
       /\ UNCHANGED orig
  /\ UNCHANGED pc

Terminate ==
  /\ pc = "Loop"
  /\ work = {}
  /\ pc' = "Done"
  /\ UNCHANGED <<a, orig, work>>

Stall ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next == Step \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Step) /\ WF_vars(Terminate)

\* Permutations written as composition with a domain automorphism.
IsPermutation(s, t) ==
  \E f \in [Domain -> Domain] :
    /\ \A i, j \in Domain : f[i] = f[j] => i = j
    /\ \A i \in Domain : s[f[i]] = t[i]

Sorted(seg) == \A i \in seg : \A j \in seg : i <= j => a[i] <= a[j]

\* The complete invariant: each work interval is a domain partition, the current
\* sequence is still a permutation of the input, and any two intervals in the
\* work set are weakly sorted with respect to each other whenever they are
\* adjacent or ordered left-to-right.
Inv ==
  /\ work # {}
  /\ \A i \in work : i.low <= i.high
  /\ \A i, j \in work : (i.low <= j.low /\ i.high <= j.high) => i = j
  /\ IsPermutation(a, orig)
  /\ \A i, j \in work : (i.high < j.low \/ Adjacent(i, j)) => Sorted(i.low..j.high)

PCorrect == pc = "Done" => (IsPermutation(a, orig) /\ Sorted(Domain))
Termination == <>(pc = "Done")

====