---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\*-----------------------------------------------------------------
\* Constants required by the .cfg file
\*-----------------------------------------------------------------
CONSTANTS Values, MaxSeqLen

\*-----------------------------------------------------------------
\* LimitedSeq replaces the unbounded Seq operator from the
\* Sequences module.  It yields only those sequences whose length
\* does not exceed MaxSeqLen.
\*-----------------------------------------------------------------
LimitedSeq(V) == { s \in Seq(V) : Len(s) <= MaxSeqLen }

\*-----------------------------------------------------------------
\* State variables
\*-----------------------------------------------------------------
VARIABLES seq, orig, work, pc

\*-----------------------------------------------------------------
\* Helper definitions
\*-----------------------------------------------------------------
\* An interval is a two‑element sequence <<low, high>> with low ≤ high.
\* We use the notation I[1] for low and I[2] for high.
\*-----------------------------------------------------------------
Intervals == { <<i, j>> : i \in 1..MaxSeqLen /\ j \in 1..MaxSeqLen /\ i <= j }

\*-----------------------------------------------------------------
\* Multi‑set (bag) of the elements of a sequence, used for
\* permutation reasoning.
\*-----------------------------------------------------------------
Bag(s) == [x \in Values |-> Cardinality({ i \in 1..Len(s) : s[i] = x })]

\* Permutation predicate
Permutes(s1, s2) == Bag(s1) = Bag(s2)

\* Sortedness predicate (non‑decreasing order)
Sorted(s) == \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

\*-----------------------------------------------------------------
\* Partition operator: given a current sequence seq, an interval I,
\* and a pivot position p, it yields all sequences that could result
\* from a correct partition of that interval.
\*-----------------------------------------------------------------
Partition(seq, I, p) ==
  LET low  == I[1]
      high == I[2]
  IN
    { s' \in LimitedSeq(Values) :
        /\ Len(s') = Len(seq)
        /\ \A i \in 1..Len(seq) :
             (i < low \/ i > high) => s'[i] = seq[i]
        /\ \A i \in low..p : \A j \in p+1..high :
               s'[i] <= s'[j]
        /\ Bag({ seq[i] : i \in low..high }) = Bag({ s'[i] : i \in low..high })
    }

\*-----------------------------------------------------------------
\* Initialisation
\*-----------------------------------------------------------------
Init ==
  /\ seq \in LimitedSeq(Values)          \* non‑empty sequence of values
  /\ Len(seq) > 0
  /\ orig = seq
  /\ work = { <<1, Len(seq)>> }          \* the whole array as the first interval
  /\ pc = "Loop"

\*-----------------------------------------------------------------
\* The main step of the algorithm (one iteration of the quicksort loop)
\*-----------------------------------------------------------------
LoopStep ==
  /\ pc = "Loop"
  /\ work # {}                            \* there is work to do
  /\ \E I \in work :
        LET low  == I[1]
            high == I[2]
        IN
          IF low = high THEN
            (* interval of length 1 – simply remove it *)
            /\ seq' = seq
            /\ orig' = orig
            /\ work' = work \ { I }
            /\ pc' = "Loop"
          ELSE
            (* choose a pivot and perform a nondeterministic partition *)
            /\ \E p \in low..high :
                 /\ \E newSeq \in Partition(seq, I, p) :
                      /\ seq' = newSeq
                      /\ orig' = orig
                      /\ (* create the two sub‑intervals, omitting empties *)
                         LET left  == IF p > low THEN { <<low, p-1>> } ELSE {}
                             right == IF p < high THEN { <<p+1, high>> } ELSE {}
                         IN work' = (work \ { I }) \cup left \cup right
                      /\ pc' = "Loop"
         

\*-----------------------------------------------------------------
\* Termination step – when there is no more work
\*-----------------------------------------------------------------
Terminate ==
  /\ pc = "Loop"
  /\ work = {}
  /\ seq' = seq
  /\ orig' = orig
  /\ work' = work
  /\ pc' = "Done"

\*-----------------------------------------------------------------
\* Stuttering step after termination (prevents deadlock)
\*-----------------------------------------------------------------
Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<seq, orig, work, pc>>

\*-----------------------------------------------------------------
\* Next-state relation
\*-----------------------------------------------------------------
Next ==
  \/ LoopStep
  \/ Terminate
  \/ Stutter

\*-----------------------------------------------------------------
\* The set of all variables, for the standard [][Next]_vars construct
\*-----------------------------------------------------------------
vars == <<seq, orig, work, pc>>

\*-----------------------------------------------------------------
\* Specification
\*-----------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\*-----------------------------------------------------------------
\* Type correctness invariant
\*-----------------------------------------------------------------
TypeOK ==
  /\ seq \in LimitedSeq(Values)
  /\ orig \in LimitedSeq(Values)
  /\ Len(orig) = Len(seq)
  /\ work \subseteq Intervals
  /\ \A I \in work :
        LET low  == I[1]
            high == I[2]
        IN low >= 1 /\ high <= Len(seq) /\ low <= high
  /\ pc \in {"Loop", "Done"}

\*-----------------------------------------------------------------
\* Main invariant used in the proof
\*-----------------------------------------------------------------
Inv ==
  /\ TypeOK
  /\ Permutes(seq, orig)                 \* the current sequence is a permutation of the original
  /\ \A I \in Intervals :
        LET low  == I[1]
            high == I[2]
        IN IF I \notin work /\ low <= high /\ high <= Len(seq)
           THEN (\A i, j \in low..high : i < j => seq[i] <= seq[j])   \* already processed intervals are sorted
           ELSE TRUE

\*-----------------------------------------------------------------
\* Partial‑correctness property: when the algorithm has terminated,
\* the final sequence is sorted and a permutation of the input.
\*-----------------------------------------------------------------
PCorrect ==
  (pc = "Done") => (Sorted(seq) /\ Permutes(seq, orig))

\*-----------------------------------------------------------------
\* Liveness property: eventual termination
\*-----------------------------------------------------------------
Termination == <> (pc = "Done")

\*-----------------------------------------------------------------
\* Exported identifiers required by the .cfg file
\*-----------------------------------------------------------------
THEOREM Spec => []Inv                \* invariant holds
THEOREM Spec => []PCorrect          \* partial correctness
THEOREM Spec => Termination         \* termination

====