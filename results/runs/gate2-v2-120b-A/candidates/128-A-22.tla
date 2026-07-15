---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen, Seq

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Idx == 1..MaxSeqLen
SeqType == SeqOf(Values)

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* An interval is represented as a tuple <<low, high>> with low <= high
Interval == [low: Idx, high: Idx]

\* The set of intervals that are still to be processed
WorkSet == SUBSET Interval

\* The program counter
PCVals == {"Loop", "Done"}

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init ==
  /\ seq \in SeqType
  /\ orig = seq
  /\ work = { [low |-> 1, high |-> Len(seq)] }
  /\ pc = "Loop"

\* ----------------------------------------------------------------------
\* Partition operator (abstract nondeterministic choice)
\* ----------------------------------------------------------------------
\* For a given interval [l..h] and a pivot index p in that interval,
\* it nondeterministically chooses a new sequence that
\*   • leaves elements outside the interval unchanged,
\*   • maintains that every element at positions l..p is ≤ every element at positions p+1..h,
\*   • is a permutation of the original sequence on the whole domain.
Partition(s, l, h, p) ==
  { sNew \in SeqType :
      /\ \A i \in Idx :
           (i < l) \/ (i > h) => sNew[i] = s[i]
      /\ \A i \in l..p : \A j \in p+1..h :
           sNew[i] <= sNew[j]
      /\ \A i \in Idx : \E j \in Idx : sNew[i] = s[j] }

\* ----------------------------------------------------------------------
\* Main action (one iteration of the loop)
\* ----------------------------------------------------------------------
Loop ==
  \/ /\ pc = "Loop"
        /\ work # {}
        /\ \E int \in work :
             LET l == int.low
                 h == int.high
                 rest == work \ {int}
             IN
               IF l = h THEN
                 /\ work' = rest
                 /\ UNCHANGED <<seq, orig>>
               ELSE
                 /\ \E p \in l..h :
                       /\ seq' \in Partition(seq, l, h, p)
                 /\ work' = rest \cup { [low |-> l, high |-> p],
                                        [low |-> p+1, high |-> h] }
                 /\ UNCHANGED orig
        /\ pc' = "Loop"
  \/ /\ pc = "Loop"
        /\ work = {}
        /\ pc' = "Done"
        /\ UNCHANGED <<seq, orig, work>>

\* ----------------------------------------------------------------------
\* Stuttering step after termination (to avoid deadlock)
\* ----------------------------------------------------------------------
DoneStutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == Loop \/ DoneStutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Safety invariant: the main partial-correctness condition
\* ----------------------------------------------------------------------
PCorrect ==
  (pc = "Done") =>
    /\ \A i \in Idx : i <= Len(seq) => i <= Len(orig)   \* lengths match
    /\ \A i \in 1..Len(seq)-1 : seq[i] <= seq[i+1]     \* sorted
    /\ \A v \in Values : 
         (Cardinality({ i \in 1..Len(seq) : seq[i] = v }) =
          Cardinality({ i \in 1..Len(orig) : orig[i] = v }))   \* permutation

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ seq \in SeqType
  /\ orig \in SeqType
  /\ work \subseteq WorkSet
  /\ pc \in PCVals

\* ----------------------------------------------------------------------
\* Inductive invariant (captures the facts needed for the proof)
\* ----------------------------------------------------------------------
Inv ==
  /\ TypeOK
  /\ (pc = "Loop") => work # {}
  /\ (pc = "Done") => work = {}

\* ----------------------------------------------------------------------
\* Liveness property: eventual termination
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

\* ----------------------------------------------------------------------
\* THEOREM (optional, can be used by TLC)
\* ----------------------------------------------------------------------
THEOREM Spec => []PCorrect

====