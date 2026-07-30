---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* A bounded version of Seq for model checking; kept FINITE so the model is
\* checkable, and kept as a replacement for Seq (do NOT declare/redefine Seq
\* itself here, as the cfg already does the replacement).
LimitedSeq(S) == CHOOSE r \in {x \in Seq(Domain(S)) : Len(x) = Len(S) /\ \A i \in Domain(S) : x[i] = S[i]}

VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

TypeOK ==
    /\ seq \in [1..MaxSeqLen -> Values]
    /\ orig \in [1..MaxSeqLen -> Values]
    /\ work \subseteq (1..MaxSeqLen \X 1..MaxSeqLen)
    /\ pc \in {"running", "terminated"}

Init ==
    /\ Len(seq) = MaxSeqLen
    /\ seq \in [1..MaxSeqLen -> Values]
    /\ orig = seq
    /\ work = {(1, MaxSeqLen)}
    /\ pc = "running"

\* Any permutation of the domain; used by the partition operator.
Auto == { f \in [1..MaxSeqLen -> 1..MaxSeqLen] : \A i, j \in Domain(f) : f[i] = f[j] => i = j }

\* Partition over the chosen interval: permute values inside the interval while
\* leaving everything outside untouched, and enforce the pivot split order.
Partitions(a, lo, hi, p) ==
    { y \in [1..MaxSeqLen -> Values] :
        \E f \in Auto :
          /\ \A k \in 1..MaxSeqLen : k < lo \/ k > hi => y[k] = a[k]
          /\ \A k \in lo..hi : y[k] = a[f[k]]
          /\ \A i \in lo..p, j \in (p+1)..hi : y[i] <= y[j] }

Step ==
    /\ pc = "running"
    /\ IF work = {}
       THEN /\ pc' = "terminated"
            /\ UNCHANGED <<seq, orig, work>>
       ELSE /\ \E lo, hi \in 1..MaxSeqLen :
              /\ <<lo, hi>> \in work
              /\ IF lo = hi
                 THEN /\ work' = work \ {<<lo, hi>>}
                      /\ UNCHANGED seq
                 ELSE /\ \E p \in lo..hi :
                        /\ \E seq2 \in Partitions(seq, lo, hi, p) :
                           /\ seq' = seq2
                           /\ work' = (work \ {<<lo, hi>>}) \cup {<<lo, p>>, <<p+1, hi>>}
            /\ UNCHANGED orig
    /\ UNCHANGED pc

Stall ==
    /\ pc = "terminated"
    /\ UNCHANGED vars

Next == Step \/ Stall

Spec == Init /\ [][Next]_vars

\* Domain is partitioned into intervals in the work set, and once an interval is
\* subdivided the two children stay disjoint, so the intervals never overlap.
Inv ==
    /\ \A lo, hi \in 1..MaxSeqLen : <<lo, hi>> \in work => lo <= hi
    /\ \A lo1, hi1, lo2, hi2 \in 1..MaxSeqLen :
         (<<lo1, hi1>> \in work /\ <<lo2, hi2>> \in work /\ lo2 <= hi1 /\ lo1 <= hi2)
           => (lo1 = lo2 /\ hi1 = hi2)
    /\ \A i \in 1..MaxSeqLen : \E j \in 1..MaxSeqLen : j = i /\ seq[i] = orig[j]
    /\ \A lo, hi \in 1..MaxSeqLen : <<lo, hi>> \in work =>
         \A i \in lo..hi - 1, j \in i+1..hi : seq[i] <= seq[j]

\* When the algorithm has terminated the sequence is a permutation of the input
\* and is sorted in non-decreasing order.
PCorrect ==
    (pc = "terminated") =>
        /\ \A i \in 1..MaxSeqLen : \E j \in 1..MaxSeqLen : j = i /\ seq[i] = orig[j]
        /\ \A i \in 1..MaxSeqLen - 1 : seq[i] <= seq[i+1]

WeakFairness == WF_vars(Step)

Termination == <>(pc = "terminated") /\ WeakFairness

====