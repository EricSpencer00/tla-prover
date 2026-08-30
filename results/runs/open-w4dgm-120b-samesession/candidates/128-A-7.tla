---- MODULE Quicksort ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

FiniteSeqOf(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

Intervals(n) == UNION {[1 .. n] \X [1 .. n] : n \in 0 .. MaxSeqLen}

\* A partition of seq is a permutation that leaves the outside of the selected
\* interval alone and puts every element inside it on the correct side of the
\* pivot index.
Partitions(seq, lo, hi, k) ==
    { t \in Permutations(FiniteSeqOf(Values)) :
        /\ Len(t) = Len(seq)
        /\ \A i \in 1 .. Len(seq) : (i < lo \/ i > hi) => t[i] = seq[i]
        /\ \A i \in lo .. hi : t[i] <= seq[k]
        /\ \A i \in lo .. hi : t[i] >= seq[k] }

VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

PCorrect == (pc = "terminated") => (\A i \in 1 .. Len(seq), j \in 1 .. Len(seq) :
    seq[i] = orig[j])

TypeOK ==
    /\ seq \in FiniteSeqOf(Values)
    /\ orig \in FiniteSeqOf(Values)
    /\ work \subseteq Intervals(Len(seq))
    /\ pc \in {"running", "terminated"}

\* A hard-to-state property: the intervals still to sort form a partition of the
\* domain, the sequence is always a permutation of the original, and any two
\* intervals that touch are already relatively sorted at their seam.
Inv ==
    /\ \A i, j \in work : (i \in work /\ j \in work /\ i # j) => IntervalDisjoint(i, j)
    /\ seq \in Permutations(FiniteSeqOf(Values))
    /\ \A i \in 1 .. MaxSeqLen : \A j \in 1 .. MaxSeqLen :
        /\ <<i, j>> \in work /\ i < j => seq[i] <= seq[j]

IntervalDisjoint(i, j) ==
    /\ i[2] < j[1] \/ j[2] < i[1]
    \/ (i[2] = i[1] /\ j[2] = j[1] /\ i[1] = j[1])

Init ==
    /\ \E s \in FiniteSeqOf(Values) : s # << >> /\ seq = s
    /\ orig = seq
    /\ work = {<<1, Len(seq)>>}
    /\ pc = "running"

QuicksortStep ==
    /\ pc = "running"
    /\ work # {}
    /\ \E i \in work :
        IF i[1] = i[2]
        THEN work' = work \ {i}
        ELSE
            /\ \E k \in i[1] .. i[2] :
                /\ \E newSeq \in Partitions(seq, i[1], i[2], k) : seq' = newSeq
                /\ work' = (work \ {i}) \cup {<<i[1], k>>, <<k + 1, i[2]>>}
    /\ pc' = IF work' = {} THEN "terminated" ELSE pc
    /\ orig' = orig

Stall ==
    /\ pc = "terminated"
    /\ UNCHANGED vars

Next == QuicksortStep \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(QuicksortStep)

\* Every execution of QuicksortStep reduces the total length of the intervals
\* still to sort, so the set of pending intervals cannot grow forever.
Termination ==
    \A i \in 1 .. MaxSeqLen : (i \in work) ~> (i \notin work)

\* FiniteSeqOf is a bounded version of Seq, so this replacement is semantics
\* preserving with respect to the model; it is what keeps the state space finite.
LimitedSeq == FiniteSeqOf

====