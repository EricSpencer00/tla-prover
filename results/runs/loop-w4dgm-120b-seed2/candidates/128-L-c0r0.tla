---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* The partition operator is redefined here as a finite version of Seq so
\* the model stays within a bounded state space; it is not a declaration.
LimitedSeq == Seq

VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

Intervals == {i \in 1..MaxSeqLen : {j \in 1..MaxSeqLen : i <= j}}

TypeOK ==
    /\ seq \in [1..MaxSeqLen -> Values]
    /\ orig \in [1..MaxSeqLen -> Values]
    /\ work \subseteq Intervals
    /\ pc \in {"loop", "done"}

Init ==
    /\ \E s \in [1..MaxSeqLen -> Values] : seq = s
    /\ orig = seq
    /\ work = {[1..MaxSeqLen]}
    /\ pc = "loop"

\* A valid partition of the interval [i..j] around pivot k: elements at or
\* below k are no greater than those above, and everything outside is unchanged.
Partition(i, j, k, s) ==
    /\ s \in [1..MaxSeqLen -> Values]
    /\ \A x \in 1..MaxSeqLen : (x < i \/ x > j) => s[x] = seq[x]
    /\ \A x \in i..k, y \in (k+1)..j : s[x] <= s[y]

Step ==
    /\ pc = "loop"
    /\ \E I \in work :
         /\ IF I[1] = I[2]
            THEN work' = work \ {I}
            ELSE
              /\ \E k \in I[1]..I[2] :
                   /\ \E s \in [1..MaxSeqLen -> Values] : Partition(I[1], I[2], k, s) /\ seq' = s
                   /\ work' = (work \ {I}) \cup {[I[1]..k], [(k+1)..I[2]]}
         /\ pc' = pc
    /\ orig' = orig

Terminate ==
    /\ pc = "loop"
    /\ work = {}
    /\ pc' = "done"
    /\ seq' = seq
    /\ orig' = orig
    /\ work' = work

Stall ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == Step \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Step) /\ WF_vars(Terminate)

\* The algorithm's partial correctness: termination yields a sorted
\* permutation of the original sequence.
PCorrect ==
    (pc = "done") =>
        /\ \E f \in [1..MaxSeqLen -> 1..MaxSeqLen] :
             /\ \A x \in 1..MaxSeqLen : orig[f[x]] = seq[x]
             /\ \A x, y \in 1..MaxSeqLen : f[x] = f[y] => x = y
        /\ \A x \in 1..(MaxSeqLen - 1) : seq[x] <= seq[x + 1]

\* The invariant is the partitioning discipline the algorithm maintains.
Inv ==
    /\ \A I \in work : I[1] <= I[2]
    /\ \A I \in work : \A x \in I[1]..I[2] : seq[x] \in Values
    /\ \A I, J \in work :
         (I # J) => (I[2] < J[1] \/ J[2] < I[1])
    /\ \A I, J \in work :
         (I[2] = J[1] /\ I # J) => seq[I[2]] <= seq[J[2]]

Termination == (pc = "loop") ~> (pc = "done")

====