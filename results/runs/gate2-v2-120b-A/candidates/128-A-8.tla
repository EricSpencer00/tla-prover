---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants required by the .cfg
\* ----------------------------------------------------------------------
CONSTANTS Values, MaxSeqLen, Seq

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Index set for a sequence of length n (1..n)
Idx(n) == 1 .. n

\* Type of a valid sequence: non‑empty, length ≤ MaxSeqLen, elements in Values
SeqOf(v) == 
    /\ Len(v) \in 1 .. MaxSeqLen
    /\ \A i \in Idx(Len(v)) : v[i] \in Values

\* Integer interval, inclusive
Interval(i, j) == { k \in Nat : i <= k /\ k <= j }

\* A proper interval for a given length n
ProperInterval(n) == { Interval(i, j) : i \in Idx(n), j \in Idx(n), i <= j }

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES seq, origSeq, workSet, pc

\* ----------------------------------------------------------------------
\* TypeOK invariant (helps TLC)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in SeqOf(seq)        \* seq is a finite sequence of Values
    /\ origSeq \in SeqOf(seq)    \* origSeq is a copy of the original
    /\ workSet \subseteq ProperInterval(Len(seq))
    /\ pc \in {"MainLoop", "Done"}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ seq = Seq                   \* Seq is a constant supplied by the .cfg
    /\ origSeq = seq
    /\ workSet = { Interval(1, Len(seq)) }
    /\ pc = "MainLoop"

\* ----------------------------------------------------------------------
\* Permutation with unchanged outside a set of indices
\* ----------------------------------------------------------------------
PermPreservingOutside(p, idxs) ==
    \A i \in Nat :
        (i \notin idxs) => p[i] = seq[i]

\* ----------------------------------------------------------------------
\* Partition step (abstract nondeterministic choice)
\* ----------------------------------------------------------------------
PartitionStep ==
    \E iv \in workSet :
        LET i == iv[1] IN
        LET j == iv[2] IN
        IF i = j THEN
            /\ workSet' = workSet \ { iv }
            /\ UNCHANGED << seq, origSeq, pc >>
        ELSE
            \E pivot \in Interval(i,j) :
                LET lower == Interval(i, pivot) IN
                LET upper == Interval(pivot+1, j) IN
                \E newSeq \in SeqOf(seq) :
                    /\ PermPreservingOutside(newSeq, iv)
                    /\ \A k \in lower, l \in upper : newSeq[k] <= newSeq[l]
                    /\ seq' = newSeq
                    /\ workSet' = (workSet \ { iv }) \cup { lower, upper }
                    /\ UNCHANGED origSeq
                    /\ pc' = "MainLoop"

\* ----------------------------------------------------------------------
\* Main loop action
\* ----------------------------------------------------------------------
MainLoop ==
    IF pc = "MainLoop" /\ workSet # {} THEN
        PartitionStep
    ELSE IF pc = "MainLoop" /\ workSet = {} THEN
        /\ pc' = "Done"
        /\ UNCHANGED << seq, origSeq, workSet >>
    ELSE
        /\ UNCHANGED << seq, origSeq, workSet, pc >>

\* ----------------------------------------------------------------------
\* Stuttering step after termination (prevents deadlock)
\* ----------------------------------------------------------------------
Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED << seq, origSeq, workSet, pc >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == MainLoop \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, origSeq, workSet, pc>>

\* ----------------------------------------------------------------------
\* Sortedness definition
\* ----------------------------------------------------------------------
Sorted(s) ==
    \A i, j \in Idx(Len(s)) : i < j => s[i] <= s[j]

\* ----------------------------------------------------------------------
\* Permutation (multiset equality) definition
\* ----------------------------------------------------------------------
Permutation(s, t) ==
    \A v \in Values :
        Cardinality({ i \in Idx(Len(s)) : s[i] = v }) =
        Cardinality({ i \in Idx(Len(t)) : t[i] = v })

\* ----------------------------------------------------------------------
\* Partial correctness invariant (the one required by the .cfg)
\* ----------------------------------------------------------------------
PCorrect ==
    /\ workSet = {}
    /\ Sorted(seq)
    /\ Permutation(seq, origSeq)

\* ----------------------------------------------------------------------
\* Full invariant used by the .cfg
\* ----------------------------------------------------------------------
Inv == /\ TypeOK
       /\ PCorrect

\* ----------------------------------------------------------------------
\* Liveness (termination) property
\* ----------------------------------------------------------------------
Termination == []<>(pc = "Done")

=======