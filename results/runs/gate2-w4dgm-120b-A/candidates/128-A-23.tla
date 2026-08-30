---- MODULE Quicksort ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* The bounded operator on the left is provided by the .cfg; we only define
\* the right side here, so Seq stays in the EXTENDS clause.
LimitedSeq(i) == IF i <= MaxSeqLen THEN i ELSE MaxSeqLen

VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

Intervals == {r \in SUBSET (1..MaxSeqLen) : \E a, b \in 1..MaxSeqLen : r = {a..b}}
Slices    == {s \in SUBSET (1..MaxSeqLen) : \E a, b \in 1..MaxSeqLen : s = {a..b}}

TypeOK ==
    /\ seq \in [1..MaxSeqLen -> Values]
    /\ orig \in [1..MaxSeqLen -> Values]
    /\ work \subseteq Intervals
    /\ pc \in {"loop", "done"}

\* The partition operator: all permutations of the slice pos..hi that leave
\* everything else alone, restricted to the pivot order.
Partition(seq, pos, hi, pivot) ==
    {seq2 \in [1..MaxSeqLen -> Values] :
        /\ \A i \in 1..MaxSeqLen : i < pos \/ i > hi => seq2[i] = seq[i]
        /\ \A i \in pos..hi : pivot <= i => seq2[i] >= seq[pivot]
        /\ \A i \in pos..hi : i <= pivot => seq2[i] <= seq[pivot]}

Init ==
    /\ \E s \in Sequences(Values) :
        /\ Len(s) >= 1
        /\ seq = [i \in 1..MaxSeqLen |-> IF i <= Len(s) THEN s[i] ELSE CHOOSE v \in Values : TRUE]
    /\ orig = seq
    /\ work = {[pos |-> 1, hi |-> Len(s)]}
    /\ pc = "loop"

Step ==
    \/ pc = "done"
    \/ \E r \in work :
        /\ work' = work \ {r}
        /\ IF r.hi = r.pos THEN pc' = pc /\ seq' = seq
           ELSE \E pivot \in r.pos..r.hi, seq2 \in Partition(seq, r.pos, r.hi, pivot) :
                /\ seq' = seq2
                /\ work' = work \cup {[pos |-> r.pos, hi |-> pivot], [pos |-> pivot + 1, hi |-> r.hi]}
                /\ pc' = pc
    \/ (work = {} /\ pc = "loop" /\ pc' = "done" /\ seq' = seq /\ work' = work)
    \/ (work = {} /\ pc = "done" /\ pc' = "done" /\ seq' = seq /\ work' = work)

Next == Step

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

Sorted ==
    /\ \A i \in 1..LimitedSeq(Len(seq)) : seq[i] \in Values
    /\ \A i \in 1..(LimitedSeq(Len(seq)) - 1) : seq[i] <= seq[i + 1]

\* Termination is not forced by the model: it is a liveness property to
\* discharge, not an ingredient of the invariant.
Termination == pc = "done"

PCorrect == pc = "done" => Sorted
TypeOKOK == TypeOK
Inv == PCorrect /\ TypeOK

====