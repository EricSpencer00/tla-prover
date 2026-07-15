---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\*----------------------------------------------------------------------
\* Constants (instantiated in the .cfg)
\*----------------------------------------------------------------------
CONSTANTS Values, MaxSeqLen, Seq

\*----------------------------------------------------------------------
\* Derived sets
\*----------------------------------------------------------------------
Indices == 1 .. MaxSeqLen

\*----------------------------------------------------------------------
\* Variable declarations
\*----------------------------------------------------------------------
VARIABLES curSeq, origSeq, workSet, pc

\*----------------------------------------------------------------------
\* Helper definitions
\*----------------------------------------------------------------------
\* An interval is represented as a pair <<l, u>> with l <= u and both in Indices
Interval == [l \in Indices, u \in Indices |-> l <= u]

\* The set of all possible intervals that fit inside the current sequence length
AllIntervals == { <<l, u>> \in [l : Indices, u : Indices] : l <= u }

\* For a given interval <<l,u>>, the set of possible pivot positions
PivotPositions(it) == l .. u

\* A permutation of the current sequence is a bijection from the index set to itself.
\* For modeling purposes we keep it abstract; the concrete definition is given
\* by the Permutes relation below.
\* 
\* The domain of the permutation is the set of indices up to the actual length of
\* the sequence, which is the length of the original sequence (since the length never
\* changes).
Domain == 1 .. Len(curSeq)

\* Permutes(s, s') holds iff s' is a permutation of s (same multiset of elements)
Permutes(s, s') ==
    /\ Len(s) = Len(s')
    /\ \A i \in 1 .. Len(s) : s'[i] \in Values
    /\ \A v \in Values : Cardinality({i \in 1 .. Len(s) : s[i] = v}) =
                         Cardinality({j \in 1 .. Len(s) : s'[j] = v})

\* PartitionResult(seq, it, p) is the set of all sequences that can result from a
\* valid partition of `seq` over interval `it` using pivot position `p`.
PartitionResult(seq, it, p) ==
    { s' \in Seq :
        /\ Len(s') = Len(seq)
        /\ \A i \in 1 .. Len(seq) : 
              (i < it[1] \/ i > it[2]) => s'[i] = seq[i]
        /\ \A i \in it[1] .. p : \A j \in p+1 .. it[2] :
              s'[i] <= s'[j]
        /\ Permutes(seq, s')
    }

\*----------------------------------------------------------------------
\* Initial state
\*----------------------------------------------------------------------
Init ==
    /\ curSeq \in Seq
    /\ Len(curSeq) > 0
    /\ Len(curSeq) <= MaxSeqLen
    /\ \A i \in 1 .. Len(curSeq) : curSeq[i] \in Values
    /\ origSeq = curSeq
    /\ workSet = { <<1, Len(curSeq)>> }
    /\ pc = "Loop"

\*----------------------------------------------------------------------
\* Actions
\*----------------------------------------------------------------------
\* Stuttering step after termination
Terminated ==
    /\ pc = "Done"
    /\ UNCHANGED <<curSeq, origSeq, workSet, pc>>

\* Main loop body
Loop ==
    /\ pc = "Loop"
    /\ IF workSet = {} THEN
          /\ pc' = "Done"
          /\ UNCHANGED <<curSeq, origSeq, workSet>>
       ELSE
          /\ \E it \in workSet :
                /\ IF it[1] = it[2] THEN
                       /\ workSet' = workSet \ {it}
                       /\ UNCHANGED <<curSeq, origSeq, pc>>
                ELSE
                       /\ \E p \in PivotPositions(it) :
                            /\ \E newSeq \in PartitionResult(curSeq, it, p) :
                                   /\ curSeq' = newSeq
                                   /\ workSet' = (workSet \ {it}) \cup { <<it[1], p>>, <<p+1, it[2]>> }
                                   /\ UNCHANGED <<origSeq, pc>>
          /\ pc' = "Loop"

\* Next-state relation
Next == Loop \/ Terminated

\*----------------------------------------------------------------------
\* Specification
\*----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<curSeq, origSeq, workSet, pc>>

\*----------------------------------------------------------------------
\* Type correctness invariant (ensures variables stay in their intended domains)
\*----------------------------------------------------------------------
TypeOK ==
    /\ curSeq \in Seq
    /\ Len(curSeq) > 0 /\ Len(curSeq) <= MaxSeqLen
    /\ origSeq = curSeq \/ (origSeq \in Seq /\ Len(origSeq) = Len(curSeq))
    /\ workSet \subseteq AllIntervals
    /\ \A it \in workSet : it[1] <= it[2] /\ it[2] <= Len(curSeq)
    /\ pc \in {"Loop", "Done"}

\*----------------------------------------------------------------------
\* Partial correctness invariant (the one called PCorrect in the .cfg)
\*----------------------------------------------------------------------
PCorrect ==
    /\ workSet = {}
    /\ \A i, j \in 1 .. Len(curSeq) : i < j => curSeq[i] <= curSeq[j]   \* sorted
    /\ Permutes(origSeq, curSeq)                                          \* permutation

\*----------------------------------------------------------------------
\* The overall inductive invariant used for model checking (named Inv in .cfg)
\*----------------------------------------------------------------------
Inv == TypeOK /\ PCorrect

\*----------------------------------------------------------------------
\* Liveness property (Termination)
\*----------------------------------------------------------------------
Termination == <> (pc = "Done")

====