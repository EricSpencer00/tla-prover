---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

\* -------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\* -------------------------------------------------
CONSTANT Values          \* Set of integer values that may appear in the sequence
CONSTANT MaxSeqLen       \* Upper bound on the length of the sequence
CONSTANT Seq             \* The initial sequence (chosen nondeterministically)

\* -------------------------------------------------
\* Helper definitions
\* -------------------------------------------------
Indices == 1..MaxSeqLen

\* An interval is a pair <<low, high>> with low <= high and both in Indices
Interval == [low : Nat, high : Nat] \* we will enforce low <= high in the code

\* The set of all intervals that are subranges of the current sequence length
AllIntervals(max) == { [low |-> l, high |-> h] : l \in 1..max, h \in l..max }

\* Permutation helper: a bijection on the domain 1..MaxSeqLen
Perm == [i \in Indices |-> i]  \* placeholder, actual permutations are built later

\* -------------------------------------------------
\* Variables
\* -------------------------------------------------
VARIABLES seq, orig, work, pc

\* -------------------------------------------------
\* Type definitions (used in TypeOK invariant)
\* -------------------------------------------------
SeqOfVals == Seq(Values)   \* the type of a finite sequence of Values

\* -------------------------------------------------
\* Initial state
\* -------------------------------------------------
Init ==
  /\ seq = Seq                     \* the initial sequence, supplied as a constant
  /\ orig = seq                    \* copy of the original sequence
  /\ work = { [low |-> 1, high |-> Len(seq)] }  \* one interval covering the whole seq
  /\ pc = "Running"

\* -------------------------------------------------
\* Utility actions
\* -------------------------------------------------
RemoveSingletonInterval ==
  /\ \E iv \in work :
        /\ iv.low = iv.high
        /\ work' = work \ {iv}
        /\ UNCHANGED <<seq, orig, pc>>
        /\ pc' = "Running"

PartitionStep ==
  /\ \E iv \in work :
        /\ iv.low < iv.high
        /\ \E p \in iv.low .. iv.high :
              LET
                lower == iv.low .. p
                upper == (p+1) .. iv.high
                unchanged == 1..(iv.low-1) \cup (iv.high+1)..Len(seq)
                newSeq == [i \in 1..Len(seq) |-> 
                            IF i \in untouched THEN seq[i]
                            ELSE IF i \in lower THEN seq[i]  \* nondet; we will allow any reorder that satisfies the ordering condition
                            ELSE IF i \in upper THEN seq[i]  \* same as above
                            ELSE seq[i]]
                untouched == unchanged
              IN
                /\ seq' = newSeq
                /\ work' = (work \ {iv}) \cup { [low |-> iv.low, high |-> p],
                                               [low |-> p+1, high |-> iv.high] }
                /\ UNCHANGED <<orig>>
                /\ pc' = "Running"
                /\ PivotPartitionCondition(seq, seq', iv, p)

\* The condition that the new sequence is a valid partition around pivot p
PivotPartitionCondition(old, new, iv, p) ==
  /\ \A i \in iv.low .. p : \A j \in (p+1) .. iv.high : new[i] <= new[j]
  /\ \A i \in 1..Len(old) : (i \notin iv.low..iv.high) => new[i] = old[i]
  /\ \A i \in iv.low..iv.high : new[i] \in Values
  /\ Length(new) = Length(old)

Terminate ==
  /\ work = {}
  /\ pc = "Terminating"
  /\ UNCHANGED <<seq, orig, work>>

Stutter ==
  /\ pc = "Terminating"
  /\ UNCHANGED <<seq, orig, work, pc>>

Next ==
  \/ /\ pc = "Running" /\ work # {}
        /\ (RemoveSingletonInterval \/ PartitionStep)
  \/ /\ pc = "Running" /\ work = {}
        /\ pc' = "Terminating"
        /\ UNCHANGED <<seq, orig, work>>
  \/ Stutter

\* -------------------------------------------------
\* Specification
\* -------------------------------------------------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* -------------------------------------------------
\* Invariants
\* -------------------------------------------------
\* TypeOK: all variables stay within their intended domains
TypeOK ==
  /\ seq \in SeqOfVals
  /\ orig \in SeqOfVals
  /\ work \subseteq AllIntervals(Len(seq))
  /\ pc \in {"Running", "Terminating"}

\* Permutation invariant: seq is always a permutation of orig
Inv ==
  /\ \A v \in Values :
        Cardinality({ i \in 1..Len(seq) : seq[i] = v }) =
        Cardinality({ i \in 1..Len(seq) : orig[i] = v })

\* PCorrect expresses the partial correctness condition when the algorithm terminates
PCorrect ==
  /\ pc = "Terminating"
  /\ \A i \in 1..Len(seq)-1 : seq[i] <= seq[i+1]

\* -------------------------------------------------
\* Liveness property (termination)
\* -------------------------------------------------
Termination ==
  <> (pc = "Terminating")

\* -------------------------------------------------
\* Theorems (optional, kept for completeness)
\* -------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Inv
THEOREM Spec => []PCorrect
THEOREM Spec => Termination

====