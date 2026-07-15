---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, TLC

VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg)
\*   Values   : the set of integer values that may appear in the sequence
\*   MaxSeqLen: the maximum length of the sequence (positive integer)
\*   Seq      : a nondeterministic sequence of length MinLen..MaxSeqLen over Values
\* ----------------------------------------------------------------------
CONSTANTS Values, MaxSeqLen, Seq

\* ----------------------------------------------------------------------
\* Types and helper definitions
\* ----------------------------------------------------------------------
Idx == 1 .. MaxSeqLen
SeqOfVals == { s \in Seq : Len(s) = MaxSeqLen }
Domain == 1 .. MaxSeqLen

Interval == [lo : Nat, hi : Nat]

\* The set of intervals that are valid subranges of the full domain
ValidInterval(i) == /\ i.lo \in Domain
                    /\ i.hi \in Domain
                    /\ i.lo <= i.hi

\* -----------------------------------------------------------------------------
\* Permutation relation (bijections on Domain)
\* ----------------------------------------------------------------------------- 
Bij == { f \in [Domain -> Domain] : 
            \A i, j \in Domain : f[i] = f[j] => i = j }

Permutes(s, t) ==
  \E f \in Bij : \A i \in Domain : t[i] = s[f[i]]

\* ----------------------------------------------------------------------
\* Partition relation for a given interval and pivot index
\* ----------------------------------------------------------------------
Partition(s, i) == 
  \E p \in Domain :
    /\ p \in i..\i.hi
    /\ \A j \in i..i.hi :
         (j <= p => s[j] <= s[p]) /\ (j > p => s[p] <= s[j])
    /\ \A j \in Domain \ (i..i.hi) : s[j] = s[j]  \* unchanged outside interval

\* A valid step of the algorithm
\* ----------------------------------------------------------------------
Step ==
  \/ /\ work # {}
     /\ \E I \in work :
        /\ ValidInterval(I)
        /\ IF I.lo = I.hi THEN
              /\ seq' = seq
              /\ work' = work \ {I}
           ELSE
              /\ \E p \in I.lo .. I.hi :
                    /\ \E newSeq \in Seq :
                         /\ Permutes(seq, newSeq)
                         /\ Partition(seq, I)   \* ensures ordering around pivot
                         /\ seq' = newSeq
              /\ work' = (work \ {I}) \cup 
                         { [lo |-> I.lo, hi |-> p] , [lo |-> p+1, hi |-> I.hi] }
  \/ /\ work = {}
     /\ seq' = seq
     /\ work' = {}
  \/ /\ pc = "Terminated"
     /\ UNCHANGED <<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ seq \in Seq
  /\ orig = seq
  /\ work = { [lo |-> 1, hi |-> Len(seq)] }
  /\ pc = "Running"

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ /\ pc = "Running"
     /\ Step
     /\ pc' = IF work' = {} THEN "Terminated" ELSE "Running"
  \/ /\ pc = "Terminated"
     /\ UNCHANGED <<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Invariant: the sequence is always a permutation of the original
\* ----------------------------------------------------------------------
Inv == Permutes(orig, seq)

\* ----------------------------------------------------------------------
\* TypeOK: simple type checking for all variables
\* ----------------------------------------------------------------------
TypeOK ==
  /\ seq \in Seq
  /\ orig \in Seq
  /\ work \subseteq { i \in Interval : ValidInterval(i) }
  /\ pc \in {"Running", "Terminated"}

\* ----------------------------------------------------------------------
\* PCorrect: partial correctness property (sorted when terminated)
\* ----------------------------------------------------------------------
Sorted(s) == \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

PCorrect == pc = "Terminated" => /\ Permutes(orig, seq)
                                 /\ Sorted(seq)

\* ----------------------------------------------------------------------
\* Liveness property: termination (handled by the .cfg)
\* ----------------------------------------------------------------------
Termination == <> (pc = "Terminated")

====