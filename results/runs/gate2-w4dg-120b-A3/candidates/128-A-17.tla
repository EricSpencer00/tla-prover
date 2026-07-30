---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen, a, b, c

VARIABLES seq, orig, work, pc
vars == <<seq, orig, work, pc>>

WorkDomain == 1..Len(seq)
Intervals == SUBSET (WorkDomain \X WorkDomain)

TypeOK ==
    /\ seq \in Seq(Values)
    /\ Len(seq) <= MaxSeqLen
    /\ Len(seq) >= 1
    /\ orig \in Seq(Values)
    /\ Len(orig) = Len(seq)
    /\ work \subseteq Intervals
    /\ pc \in {"Looping", "Terminated"}

\* The permutation set is built so that each interval's segment may be
\* handled independently; a segment that has already been sorted is frozen
\* and can only be moved as a unit via a domain automorphism, never split.
\* This is what lets the invariant state the lower interval is sorted
\* relative to the upper one without ever having to look at the contents.
DomainPartitions ==
    \E F \in [WorkDomain -> WorkDomain] :
        /\ \A i \in WorkDomain : F[i] >= 1
        /\ \A i, j \in WorkDomain : F[i] = F[j] => i = j
        /\ \A i \in WorkDomain : seq[i] = orig[F[i]]
        /\ \A a, b \in WorkDomain :
            (a < b /\ \A i \in WorkDomain : F[i] <= a \/ F[i] >= b) => seq[a] <= seq[b]

\* Permutation of the input sequence (the actual sorting work).
Permutation ==
    \E f \in [WorkDomain -> WorkDomain] :
        /\ \A i \in WorkDomain : f[i] >= 1
        /\ \A i, j \in WorkDomain : f[i] = f[j] => i = j
        /\ \A i \in WorkDomain : seq[i] = orig[f[i]]

\* A partition that keeps the outside untouched and the below-pivot side
\* weakly below the above-pivot side; applied only inside an interval.
ValidPartition(a, b) ==
    /\ b \in WorkDomain
    /\ a \in 1..b
    /\ \E y \in Sequences(Values) :
        /\ \A i \in WorkDomain : i < a \/ i >= b => y[i] = seq[i]
        /\ \A i \in 1..b : i >= a => \A j \in b+1..Len(seq) : y[i] <= y[j]
        /\ y

\* The full invariant: partitioning is well behaved, the sequence is a
\* permutation of the input, and the lower side of any chosen pivot is
\* sorted relative to the upper side.
Inv ==
    /\ DomainPartitions
    /\ Permutation
    /\ \A a, b \in WorkDomain : ValidPartition(a, b)

Init ==
    /\ Len(seq) \in 1..MaxSeqLen
    /\ \E x \in Sequences(Values) : Len(x) = Len(seq) /\ seq = x
    /\ orig = seq
    /\ work = {<<1, Len(seq)>>}
    /\ pc = "Looping"

\* One iteration of the sorting loop; the partition result is nondeterministic
\* over the set of partitions the algorithm could have produced.
Step ==
    /\ pc = "Looping"
    /\ work # {}
    /\ \E i, j \in WorkDomain :
        /\ <<i, j>> \in work
        /\ j \in 1..Len(seq)
        /\ IF i = j
           THEN work' = work \ {{i, j}}
           ELSE /\ work' = (work \ {{i, j}}) \cup {<<i, j-1>>, <<j+1, Len(seq)>>}
                /\ seq' \in ValidPartition(i, j)
        /\ pc' = "Looping"
    /\ orig' = orig

Terminate ==
    /\ pc = "Looping"
    /\ work = {}
    /\ pc' = "Terminated"
    /\ seq' = seq
    /\ work' = work
    /\ orig' = orig

Stall ==
    /\ pc = "Terminated"
    /\ UNCHANGED vars

Next == Step \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Step) /\ WF_vars(Terminate)

PCorrect ==
    \/ pc = "Looping"
    \/ (pc = "Terminated" /\ \A i \in 1..Len(seq) : \A j \in 1..Len(seq) : i <= j => seq[i] <= seq[j])

Termination == <>(pc = "Terminated")
====