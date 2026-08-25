---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

\* ---------------------------------------------------------------------------
\* Constants required by the .cfg file
\* ---------------------------------------------------------------------------
CONSTANTS Values, MaxSeqLen

\* ---------------------------------------------------------------------------
\* Helper definitions
\* ---------------------------------------------------------------------------
LimitedSeq(V) == { s \in Seq(V) : Len(s) <= MaxSeqLen }

Interval == <<l, h>>  \* a pair of natural numbers representing a contiguous range
IntervalRange(i) == i[1] .. i[2]   \* the set of indices covered by interval i

Count(seq, v) == 
    Cardinality({ i \in 1..Len(seq) : seq[i] = v })

Permutation(s1, s2) == 
    /\ Len(s1) = Len(s2)
    /\ \A v \in Values : Count(s1, v) = Count(s2, v)

Sorted(seq) == 
    \A i, j \in 1..Len(seq) : i < j => seq[i] <= seq[j]

Partition(seq, intv, p) ==
    { s' \in Seq(Values) :
        /\ Len(s') = Len(seq)
        /\ \A j \in 1..Len(seq) :
              (j \notin IntervalRange(intv)) => s'[j] = seq[j]
        /\ \A v \in Values :
              Count( [j \in IntervalRange(intv) |-> seq[j]], v) =
              Count( [j \in IntervalRange(intv) |-> s'[j]], v)
        /\ \A j \in IntervalRange(intv), k \in IntervalRange(intv) :
              (j <= p /\ k > p) => s'[j] <= s'[k] }

\* ---------------------------------------------------------------------------
\* Variables
\* ---------------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\* ---------------------------------------------------------------------------
\* Types and invariants
\* ---------------------------------------------------------------------------
TypeOK ==
    /\ seq \in LimitedSeq(Values) /\ seq # <<>>
    /\ orig \in LimitedSeq(Values) /\ orig = seq
    /\ work \subseteq { i \in Interval : 
                       i[1] >= 1 /\ i[1] <= i[2] /\ i[2] <= Len(seq) }
    /\ pc \in {"Loop", "Done"}

\* The set of indices that are still unfinished
CoveredIndices == UNION { IntervalRange(i) : i \in work }

\* The set of indices that are already completed (outside work)
DoneIndices == (1..Len(seq)) \ CoveredIndices

Inv ==
    /\ Permutation(seq, orig)
    /\ \A i \in work : i[1] <= i[2] /\ i[2] <= Len(seq)
    /\ \A i, j \in DoneIndices : i < j => seq[i] <= seq[j]

PCorrect ==
    (pc = "Done") => (Sorted(seq) /\ Permutation(seq, orig))

\* ---------------------------------------------------------------------------
\* Initial state
\* ---------------------------------------------------------------------------
Init ==
    /\ seq \in LimitedSeq(Values) /\ seq # <<>>
    /\ orig = seq
    /\ work = { <<1, Len(seq)>> }
    /\ pc = "Loop"

\* ---------------------------------------------------------------------------
\* Next-state relation
\* ---------------------------------------------------------------------------
Step ==
    \/ \E i \in work :
          /\ i[1] = i[2]               \* singleton interval
          /\ work' = work \ {i}
          /\ UNCHANGED <<seq, orig, pc>>
    \/ \E i \in work, p \in IntervalRange(i) :
          /\ i[1] < i[2]               \* interval longer than one element
          /\ LET lower == <<i[1], p>>
                 upper == <<p+1, i[2]>>
                 newWork == (work \ {i}) 
                            \cup {lower} 
                            \cup (IF p < i[2] THEN {upper} ELSE {})
             IN
               /\ work' = newWork
               /\ \E s \in Partition(seq, i, p) :
                      /\ s \in LimitedSeq(Values)
                      /\ seq' = s
               /\ UNCHANGED orig
               /\ pc' = "Loop"
    \/ /\ work = {}
          /\ pc' = "Done"
          /\ UNCHANGED <<seq, orig, work>>
    \/ /\ pc = "Done"
          /\ UNCHANGED <<seq, orig, work, pc>>

Next == Step

\* ---------------------------------------------------------------------------
\* Specification
\* ---------------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* ---------------------------------------------------------------------------
\* Temporal properties
\* ---------------------------------------------------------------------------
Termination == <> (pc = "Done")

\* ---------------------------------------------------------------------------
\* Exported identifiers for the model checker
\* ---------------------------------------------------------------------------
THEOREM Spec => []Inv
THEOREM Spec => []PCorrect

\* Provide the required names for the .cfg file
\* (they are already defined above)
====