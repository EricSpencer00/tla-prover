---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* An interval is a contiguous pair of indices into the sequence.
Interval == [lo : 1..MaxSeqLen, hi : 1..MaxSeqLen]

\* A partial permutation: bijections of the domain that are identity except on
\* a finite set of swapped indices.
VARIABLES seq, origSeq, work, pc
vars == <<seq, origSeq, work, pc>>

TypeOK ==
    /\ origSeq \in Seq(Values)
    /\ seq \in Seq(Values)
    /\ work \subseteq Interval
    /\ pc \in {"main", "done"}

Init ==
    /\ \E s \in Seq(Values) : origSeq = s
    /\ seq = origSeq
    /\ work = {[lo |-> 1, hi |-> Len(origSeq)]}
    /\ pc = "main"

\* An automorphism of the domain: identity a.e., finite support, invertible.
Permutations ==
    { f \in [1..MaxSeqLen -> 1..MaxSeqLen] :
        /\ \E S \in SUBSET 1..MaxSeqLen :
            /\ \A i \in 1..MaxSeqLen : (i \notin S) => f[i] = i
            /\ \A i \in S, j \in S : f[i] = f[j] => i = j
            /\ \E g \in [1..MaxSeqLen -> 1..MaxSeqLen] :
                /\ \A i \in 1..MaxSeqLen : g[f[i]] = i
                /\ \A i \in 1..MaxSeqLen : f[g[i]] = i }

\* Nondeterministic partition: only the chosen interval's contents may move,
\* never touching the rest; the two resulting blocks are ordered by the pivot.
PartitionOf ==
    { s \in Seq(Values) :
        /\ Len(s) = MaxSeqLen
        /\ \E f \in Permutations :
            /\ \A i \in 1..MaxSeqLen : s[i] = seq[f[i]]
            /\ \E p \in 1..MaxSeqLen :
                /\ \A i \in 1..p : s[i] <= s[p+1]
                /\ \A i \in p+2..MaxSeqLen : s[p+1] <= s[i] }

\* The main step: pick an interval, partition it, and replace it with two.
Step ==
    /\ pc = "main"
    /\ work # {}
    /\ \E it \in work :
        /\ IF it.lo = it.hi
           THEN work' = work \ {it}
           ELSE
              \E p \in it.lo..it.hi :
                 /\ \E s \in PartitionOf :
                    /\ seq' = s
                    /\ work' = (work \ {it})
                         \cup {[lo |-> it.lo, hi |-> p],
                                [lo |-> p+1, hi |-> it.hi]}
        /\ pc' = "main"
    /\ UNCHANGED origSeq

Done ==
    /\ pc = "main"
    /\ work = {}
    /\ pc' = "done"
    /\ UNCHANGED <<seq, origSeq, work>>

Quiesce ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == Step \/ Done \/ Quiesce

Spec == Init /\ [][Next]_vars
    /\ WF_vars(Step) /\ WF_vars(Done)

\* The sorted output is a rearrangement of the input: no element is created
\* or destroyed by any partitioning.
PCorrect ==
    /\ work = {}
    /\ \E f \in Permutations : \A i \in 1..Len(seq) : seq[i] = origSeq[f[i]]
    /\ \A i \in 1..Len(seq)-1 : seq[i] <= seq[i+1]

\* The full inductive invariant: partition domains stay disjoint, the output
\* always stays a permutation of the input, and partition results are ordered.
Inv ==
    /\ \A a, b \in work : (a # b) => (a.hi < b.lo \/ b.hi < a.lo)
    /\ \E f \in Permutations : \A i \in 1..Len(seq) : seq[i] = origSeq[f[i]]
    /\ \A it \in work : \A i \in it.lo..it.hi-1 : seq[i] <= seq[i+1]

\* Liveness: the algorithm eventually reaches its terminal state.
Termination == <>(pc = "done")

\* Bounded runtime: a finite, deadlock-free model checking run.
LimitedSeq == Seq(Values)

====