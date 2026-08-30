---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

Intervals == [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]
Automorphisms == {f \in [1..MaxSeqLen -> 1..MaxSeqLen] : f \in [1..MaxSeqLen -> 1..MaxSeqLen] /\ \A i, j \in 1..MaxSeqLen : (i # j) => (f[i] # f[j])}
\* The partition operator is finite because it only permutes a bounded interval of a bounded-length sequence.
Nxt(s, r, p) == {p} \cup {j \in r : j # p}
BelowEq(r, p, v) == \A j \in r : (j <= p) => (s[j] <= v)
AboveGe(r, p, v) == \A j \in r : (j > p) => (v <= s[j])
ValidPartition(s, r, p, v) == BelowEq(r, p, v) /\ AboveGe(r, p, v)
Permutations(s, r) == {t \in [1..MaxSeqLen -> Values] : \E f \in Automorphisms : \A j \in r : t[j] = s[f[j]] /\ \A j \in (1..MaxSeqLen) \ r : t[j] = s[j]}
Functions == [dom: 1..MaxSeqLen, ran: Values]

VARIABLES seq, orig, workset, pc

vars == <<seq, orig, workset, pc>>

TypeOK ==
    /\ seq \in Functions
    /\ orig \in Functions
    /\ workset \subseteq Intervals
    /\ pc \in {"Loop", "Done"}

Init ==
    /\ \E s \in {f \in Functions : f.dom = 1..MaxSeqLen /\ f.ran \subseteq Values} : seq = s /\ orig = s
    /\ workset = {[lo |-> 1, hi |-> MaxSeqLen]}
    /\ pc = "Loop"

Split(i) == [lo |-> i.lo, hi |-> i.hi]

Step ==
    /\ pc = "Loop"
    /\ \E i \in workset :
         /\ IF i.lo = i.hi THEN workset' = workset \ {i}
            ELSE \E p \in i.lo..i.hi :
                 /\ \E v \in Values :
                      /\ ValidPartition(seq, Nxt(seq, i, p), p, v)
                      /\ seq' = [seq EXCEPT ![Nxt(seq, i, p)] = v]
                 /\ workset' = (workset \ {i}) \cup {[lo |-> i.lo, hi |-> p], [lo |-> p + 1, hi |-> i.hi]}
    /\ pc' = pc

Terminate ==
    /\ pc = "Loop"
    /\ workset = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<seq, orig, workset>>

Next == Step \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(Step) /\ WF_vars(Terminate)

Sorted == \A i \in 1..(MaxSeqLen - 1) : seq[i] <= seq[i + 1]
Permutation == \A j \in 1..MaxSeqLen : \E k \in 1..MaxSeqLen : orig[k] = seq[j]

PCorrect == (pc = "Done") => (Sorted /\ Permutation)

SortedBelow(i) == \A a, b \in 1..MaxSeqLen : (a <= i /\ b <= i) => (seq[a] <= seq[b])
BelowUnchanged(i) == \A a \in 1..i : seq[a] = orig[a]
AboveSorted(i) == \A a, b \in (i + 1)..MaxSeqLen : (a <= b) => (seq[a] <= seq[b])

Inv == /\ BelowUnchanged(1) /\ AboveSorted(1)
        /\ \A i \in 1..(MaxSeqLen - 1) : SortedBelow(i) /\ BelowUnchanged(i) /\ AboveSorted(i)

Termination == (pc = "Loop") ~> (pc = "Done")
====