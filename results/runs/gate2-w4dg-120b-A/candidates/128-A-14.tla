---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Values
CONSTANT MaxSeqLen
CONSTANT Seq

\* The sort rewrites the full sequence but only ever moves elements inside the
\* actively partitioned interval; elements outside stay untouched.
VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

Intervals == [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]
Dom == 1..MaxSeqLen

TypeOK ==
  /\ seq \in Seq
  /\ orig \in Seq
  /\ work \subseteq Intervals
  /\ pc \in {"loop", "done"}

Init ==
  /\ seq = CHOOSE s \in Seq : TRUE
  /\ orig = seq
  /\ work = {[lo |-> 1, hi |-> Len(seq)]}
  /\ pc = "loop"

\* A valid partition of the current interval under the chosen pivot must leave
\* outside elements untouched and place all "lower" elements no later than any
\* "upper" element in the resulting sequence.
ValidPart(s, t, i, lo, hi) ==
  /\ \A k \in Dom \ (k < lo \/ k > hi) : s[k] = t[k]
  /\ \A l, r \in lo..hi :
       (l <= i /\ r > i) => t[l] <= t[r]

Step ==
  /\ pc = "loop"
  /\ work # {}
  /\ \E iv \in work :
       /\ \E i \in iv.lo..iv.hi :
            /\ \E t \in Seq :
                 /\ ValidPart(seq, t, i, iv.lo, iv.hi)
                 /\ seq' = t
            /\ work' = (work \ {iv})
                 \cup {[lo |-> iv.lo, hi |-> i], [lo |-> i + 1, hi |-> iv.hi]}
       /\ (Len(seq) = iv.lo /\ work' = work \ {iv})
  /\ pc' = "loop"

Terminate ==
  /\ pc = "loop"
  /\ work = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, orig, work>>

Unchanged == pc = "done" /\ UNCHANGED vars

Next == Step \/ Terminate \/ Unchanged

Spec == Init /\ [][Next]_vars /\ WF_vars(Step) /\ WF_vars(Terminate)

\* The permutation predicate is defined via domain automorphisms.
Automorphisms ==
  { f \in [Dom -> Dom] : (f \in (DOMAIN Seq)) /\ (\A i \in Dom : i <= Len(seq) => f[i] <= Len(seq)) }

IsPerm(s, t) ==
  \E f \in Automorphisms :
    \A k \in Dom : t[f[k]] = s[k]

\* The invariant tracks domain partitions, permutation preservation, and the
\* sortedness that holds between any two active intervals.
Inv ==
  /\ \E lo, hi \in Dom :
       /\ lo <= hi
       /\ work = {[lo |-> lo, hi |-> hi]}
       /\ \A i \in Dom : i > hi => seq[i] = orig[i]
  /\ IsPerm(seq, orig)
  /\ \A j \in work, k \in work :
       (j.hi <= k.lo /\ j.hi > 0 /\ k.lo > 0) => seq[j.hi] <= seq[k.lo]

PCorrect ==
  /\ pc = "done"
  => /\ IsPerm(seq, orig)
     /\ \A i \in 1..(Len(seq) - 1) : seq[i] <= seq[i + 1]

Termination ==
  pc = "done"

====