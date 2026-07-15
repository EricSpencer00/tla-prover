---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\* Constants (to be instantiated by the .cfg module)
\* ----------------------------------------------------------------------
CONSTANTS Values, MaxSeqLen, Seq

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* An index is a positive integer up to the current length of the sequence.
Idx(s) == 1 .. Len(s)

\* Intervals are pairs <<i, j>> with i <= j.
INTERVAL == { <<i, j>> : i, j \in Nat, i <= j }

\* Domain of an interval: the set of indices it covers.
Domain(i) == i[1] .. i[2]

\* The algorithm maintains a set of intervals that are still to be processed.
\* Initially this set contains the whole sequence.
InitialWorkSet == { <<1, Len(Seq)>> }

\* A sequence is a function from its index set to Values.
SeqType == [i \in Nat |-> Values]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES curSeq, origSeq, workSet, pc

\* ----------------------------------------------------------------------
\* Type correctness (used as a separate invariant)
\* ----------------------------------------------------------------------
TypeOK ==
  /\ curSeq \in SeqType
  /\ origSeq \in SeqType
  /\ workSet \subseteq INTERVAL
  /\ pc \in {"Running", "Done"}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ curSeq = Seq
  /\ origSeq = Seq
  /\ workSet = InitialWorkSet
  /\ pc = "Running"

\* ----------------------------------------------------------------------
\* Update the set of intervals after processing \@i
\* ----------------------------------------------------------------------
UpdateWorkSet(ws, i) ==
  IF i[1] = i[2] THEN
    ws \ {i}
  ELSE
    LET pivot \in i[1] .. i[2]
        lsub == <<i[1], pivot - 1>>
        rsub == <<pivot + 1, i[2]>>
        newWs == ws \ {i}
    IN
      (newWs \cup
        (IF lsub[1] <= lsub[2] THEN {lsub} ELSE {})
        \cup
        (IF rsub[1] <= rsub[2] THEN {rsub} ELSE {})
      )

\* ----------------------------------------------------------------------
\* Partition step – nondeterministically choose a new sequence that
\*   (a) leaves elements outside the interval unchanged,
\*   (b) respects the pivot ordering property.
\* ----------------------------------------------------------------------
Partition(cur, i) ==
  LET pivot \in i[1] .. i[2] IN
    { new |
      /\ new \in SeqType
      /\ \A k \in Idx(cur) :
            (k \notin Domain(i) => new[k] = cur[k])
      /\ \A k1 \in i[1] .. pivot :
            \A k2 \in pivot + 1 .. i[2] :
                new[k1] <= new[k2]
    }

\* ----------------------------------------------------------------------
\* Main step of the algorithm
\* ----------------------------------------------------------------------
Step ==
  \/ /\ pc = "Running"
        /\ workSet # {}
        /\ \E i \in workSet :
            /\ curSeq' \in Partition(curSeq, i)
            /\ workSet' = UpdateWorkSet(workSet, i)
            /\ origSeq' = origSeq
            /\ pc' = "Running"
  \/ /\ pc = "Running"
        /\ workSet = {}
        /\ pc' = "Done"
        /\ UNCHANGED <<curSeq, origSeq, workSet>>

\* Stuttering step after termination to avoid deadlock
TerminateStutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<curSeq, origSeq, workSet, pc>>

Next == Step \/ TerminateStutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<curSeq, origSeq, workSet, pc>>

\* ----------------------------------------------------------------------
\* Safety property: partial correctness (Invariant)
\* ----------------------------------------------------------------------
Sorted(s) == \A i, j \in Idx(s) : i < j => s[i] <= s[j]

Permutation(s, t) ==
  \E f \in [Idx(s) -> Idx(s)] :
    /\ \A i \in Idx(s) : f[i] \in Idx(s)
    /\ \A i, j \in Idx(s) : f[i] = f[j] => i = j
    /\ \A i \in Idx(s) : t[i] = s[f[i]]

PCorrect ==
  (pc = "Done") => (Sorted(curSeq) /\ Permutation(origSeq, curSeq))

\* ----------------------------------------------------------------------
\* Additional invariant used by the .cfg file
\* ----------------------------------------------------------------------
Inv == PCorrect

\* ----------------------------------------------------------------------
\* Liveness property (termination)
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

\* ----------------------------------------------------------------------
\* Theorems (optional, for TLAPS)
\* ----------------------------------------------------------------------
THEOREM Spec => []PCorrect

====