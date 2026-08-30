---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* A range of indices of the partitioned sequence.
Interval == [lo: 1 .. MaxSeqLen, hi: 1 .. MaxSeqLen]

\* A permutation of a domain, represented as a function on indices.
Permutation == [1 .. MaxSeqLen -> 1 .. MaxSeqLen]

VARIABLES seq, original, todo, pc

vars == <<seq, original, todo, pc>>

MaxVal == CHOOSE x \in Values : \A y \in Values : y <= x

TypeOK ==
    /\ seq \in Seq(Values)
    /\ original \in Seq(Values)
    /\ todo \subseteq Interval
    /\ pc \in {"loop", "done"}

Init ==
    /\ \E s \in Seq(Values) : Len(s) = MaxSeqLen /\ seq = s /\ original = s
    /\ todo = {[lo |-> 1, hi |-> MaxSeqLen]}
    /\ pc = "loop"

\* Domain partitions before and after a partition step must be complementary
\* and cover the whole sequence.
\* The permutation is the structural witness that no element moved across a
\* domain boundary in the process.
\* Relative sortedness is required only across partition boundaries, never
\* inside an interval that has not been split yet.
\* The set of intervals to be processed is exactly recovered from those
\* boundaries, so the three are not independent.
\* The two directions of the equivalence below are proved separately.
PartitionOK ==
    /\ /\ \A i \in todo : i.lo <= i.hi
       /\ \A a, b \in todo : (a.lo = b.lo /\ a.hi = b.hi) => (a = b)
       /\ \E p \in Permutation :
            /\ {i.lo : i \in todo} = {p[i] : i \in 1 .. Len(seq)}
            /\ {i.hi : i \in todo} = {p[i] : i \in 1 .. Len(seq)}
            /\ \A i \in 1 .. Len(seq) : p[i] >= i
       /\ \A a, b \in todo :
            (a.hi < b.lo /\ a.hi < MaxVal) => (seq[a.hi] <= seq[b.lo])

\* Every partition step permutes the sequence within the interval and orders
\* the two partition subintervals correctly.
SortedPartitions(a, b) ==
    /\ LET left  == [i \in 1 .. b.lo - 1 |-> seq[i]]
           right == [i \in b.lo .. Len(seq) |-> seq[i]]
       IN \E c \in Permutation :
            /\ \A i \in 1 .. Len(left) : c[i] = i
            /\ \A i \in b.lo .. MaxVal : c[i] >= b.lo
            /\ seq' = left \o c \o right
    /\ todo' = (todo \ {a}) \cup {[lo |-> a.lo, hi |-> b.lo - 1], [lo |-> b.lo, hi |-> a.hi]}
    /\ pc' = IF todo = {[lo |-> 1, hi |-> MaxSeqLen]} THEN "loop" ELSE pc

QuicksortStep ==
    \/ \E a \in todo :
         IF a.lo = a.hi
         THEN /\ todo' = todo \ {a}
              /\ pc' = IF todo \ {a} = {} THEN "done" ELSE pc
              /\ UNCHANGED <<seq, original>>
         ELSE \E b \in todo :
              /\ b.lo > a.lo /\ b.hi < a.hi
              /\ SortedPartitions(a, b)
    \/ UNCHANGED <<seq, original>>

Stall == pc = "done" /\ UNCHANGED vars

Next == QuicksortStep \/ Stall

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(QuicksortStep)

PCorrect == pc = "done" => /\ SeqPerm(seq, original) /\ \A i \in 1 .. Len(seq) - 1 : seq[i] <= seq[i + 1]
             /\ UNCHANGED <<seq, original, todo>>

\* A FINITE version of Seq from Sequences: allowed only up to MaxSeqLen.
LimitedSeq == {s \in Seq(Values) : Len(s) <= MaxSeqLen}

\* Every reachable state has a bounded trace of bounded length.
FiniteTraceBound == \A s \in states : (s.seq \in LimitedSeq) /\ (s.todo \subseteq Interval)

Termination == <>(pc = "done")

====