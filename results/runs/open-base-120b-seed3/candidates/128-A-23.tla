---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, Integers, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants required by the .cfg file
\* ----------------------------------------------------------------------
CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* A finite version of Seq that respects the bound MaxSeqLen
\* ----------------------------------------------------------------------
LimitedSeq == { s \in Seq(Values) : Len(s) <= MaxSeqLen }

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
IntLow(int) == int[1]
IntHigh(int) == int[2]

Intervals(s) ==
  { <<l, h>> \in (1 .. Len(s)) \X (1 .. Len(s)) :
      l <= h }

Count(s, v) ==
  Cardinality({ i \in 1 .. Len(s) : s[i] = v })

IsPermutation(s1, s2) ==
  Len(s1) = Len(s2) /\ 
  \A v \in Values : Count(s1, v) = Count(s2, v)

Sorted(s) ==
  \A i, j \in 1 .. Len(s) : i < j => s[i] <= s[j]

\* ----------------------------------------------------------------------
\* Partition operator – nondeterministically chooses any valid
\* partition of the interval [l..h] around pivot p
\* ----------------------------------------------------------------------
Partition(s, int, p) ==
  { s2 \in LimitedSeq :
      Len(s2) = Len(s) /\
      \A i \in 1 .. Len(s) :
        (i < IntLow(int) \/ i > IntHigh(int)) => s2[i] = s[i] /\
      \A i \in IntLow(int) .. p :
        \A j \in p+1 .. IntHigh(int) : s2[i] <= s2[j] /\
      IsPermutation(s2, s) }

\* ----------------------------------------------------------------------
\* Type correctness predicate
\* ----------------------------------------------------------------------
TypeOK ==
  /\ seq \in LimitedSeq
  /\ orig \in LimitedSeq
  /\ Len(seq) = Len(orig)
  /\ work \subseteq Intervals(seq)
  /\ pc \in {"Loop", "Done"}

\* ----------------------------------------------------------------------
\* Invariant used for checking
\* ----------------------------------------------------------------------
Inv == TypeOK /\ IsPermutation(seq, orig)

\* ----------------------------------------------------------------------
\* Partial correctness predicate (to be used as an invariant)
\* ----------------------------------------------------------------------
PCorrect ==
  (pc = "Done") => (Sorted(seq) /\ IsPermutation(seq, orig))

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init ==
  /\ \E s \in LimitedSeq : Len(s) > 0
  /\ seq = s
  /\ orig = s
  /\ work = { <<1, Len(s)>> }
  /\ pc = "Loop"

\* ----------------------------------------------------------------------
\* Main step of the algorithm
\* ----------------------------------------------------------------------
LoopStep ==
  /\ pc = "Loop"
  /\ work # {}
  /\ \E int \in work :
        LET low == IntLow(int) IN
        LET high == IntHigh(int) IN
        IF low = high THEN
          /\ seq' = seq
          /\ orig' = orig
          /\ work' = work \ {int}
          /\ pc' = "Loop"
        ELSE
          /\ \E p \in low .. high :
                /\ \E s2 \in Partition(seq, int, p) :
                     /\ seq' = s2
                     /\ orig' = orig
                     /\ work' = (work \ {int}) \cup { <<low, p>>, <<p+1, high>> }
                     /\ pc' = "Loop"
        \* (All other variables unchanged)
        /\ UNCHANGED <<orig>>

\* ----------------------------------------------------------------------
\* Termination step
\* ----------------------------------------------------------------------
Terminate ==
  /\ pc = "Loop"
  /\ work = {}
  /\ pc' = "Done"
  /\ UNCHANGED <<seq, orig, work>>

\* ----------------------------------------------------------------------
\* Stuttering after termination (to keep the model from deadlocking)
\* ----------------------------------------------------------------------
Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == LoopStep \/ Terminate \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_(<<seq, orig, work, pc>>)

\* ----------------------------------------------------------------------
\* Liveness property: eventual termination
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

\* ----------------------------------------------------------------------
\* The set of invariants to be checked (named in the .cfg file)
\* ----------------------------------------------------------------------
\* (These are simply the operators defined above.)
\* PCorrect, TypeOK, Inv

====