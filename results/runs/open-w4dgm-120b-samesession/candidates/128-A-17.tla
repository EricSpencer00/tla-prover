---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

Intervals == [lo: 1..MaxSeqLen, hi: 1..MaxSeqLen]

VARIABLES seq, original, workset, pc

vars == <<seq, original, workset, pc>>

TypeOK ==
    /\ seq \in Seq(Values)
    /\ Len(seq) <= MaxSeqLen
    /\ original \in Seq(Values)
    /\ Len(original) <= MaxSeqLen
    /\ workset \subseteq Intervals
    /\ pc \in {"loop", "done"}

PartitionOver(i, v, w, lo, hi) ==
    /\ \A k \in 1..(lo - 1) : w[k] = v[k]
    /\ \A k \in hi..Len(v) : w[k] = v[k]
    /\ \A a \in lo..i, b \in (i + 1)..hi : w[a] <= w[b]

Permutations(v) ==
    {w \in Seq(Values) : \E f \in [1..Len(v) -> 1..Len(v)] :
        /\ \A x \in 1..Len(v) : \E y \in 1..Len(v) : f[x] = y
        /\ \A y \in 1..Len(v) : \E x \in 1..Len(v) : f[x] = y
        /\ \A x \in 1..Len(v) : w[x] = v[f[x]]}

Init ==
    /\ \E s \in Seq(Values) :
        /\ Len(s) > 0 /\ Len(s) <= MaxSeqLen
        /\ seq = s
        /\ original = s
    /\ workset = {[lo |-> 1, hi |-> Len(seq)]}
    /\ pc = "loop"

Step ==
    /\ pc = "loop"
    /\ \E iv \in workset :
        /\ workset' = workset \ {iv}
        /\ IF iv.lo = iv.hi
           THEN workset' = workset'
           ELSE
               \/ \E i \in iv.lo..iv.hi :
                    /\ \E w \in PartitionOver(i, seq, Permutations(seq), iv.lo, iv.hi) :
                         seq' = w
                    /\ workset' = workset' \cup {[lo |-> iv.lo, hi |-> i], [lo |-> i + 1, hi |-> iv.hi]}
        /\ pc' = pc
    /\ original' = original

Terminate ==
    /\ pc = "loop"
    /\ workset = {}
    /\ pc' = "done"
    /\ UNCHANGED <<seq, original, workset>>

Stall ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == Step \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars /\ SF_Vars(Step) /\ SF_Vars(Terminate)

InWorkset(i) == \E iv \in workset : iv.lo <= i /\ i <= iv.hi

DomainPartitions ==
    /\ { i \in 1..Len(seq) : \E iv \in workset : iv.lo = i } = {1}
    /\ \A i \in 1..Len(seq) : i < Len(seq) => (InWorkset(i) <=> ~InWorkset(i + 1))

PermutationPreserved == \E f \in [1..Len(seq) -> 1..Len(seq)] :
    /\ \A x \in 1..Len(seq) : \E y \in 1..Len(seq) : f[x] = y
    /\ \A y \in 1..Len(seq) : \E x \in 1..Len(seq) : f[x] = y
    /\ \A x \in 1..Len(seq) : seq[x] = original[f[x]]

RelativeSortedness == \A iv \in workset, i \in iv.lo..(iv.hi - 1) : seq[i] <= seq[i + 1]

Inv == DomainPartitions /\ PermutationPreserved /\ RelativeSortedness

PCorrect == (pc = "done") => (Inv /\ Len(seq) = Len(original))

Termination == (pc = "done") ~> (pc = "loop")

\* Replace the unbounded Seq with a bounded version so the model is finite.
LimitedSeq == [f \in [1..MaxSeqLen -> Values] |-> <<f[1], f[2], f[3]>>]

====