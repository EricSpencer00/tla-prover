---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\*-----------------------------------------------------------------
\* Constants
\*-----------------------------------------------------------------
CONSTANTS Values, MaxSeqLen

\*-----------------------------------------------------------------
\* Operator replacing Seq from Sequences with a bounded version
\*-----------------------------------------------------------------
LimitedSeq == { s \in Seq(Values) : Len(s) <= MaxSeqLen }

\*-----------------------------------------------------------------
\* Helper definitions
\*-----------------------------------------------------------------
Interval == <<i, j>>  \* pair of indices with i <= j

Intervals(seq) == 
  { <<i, j>> \in Interval :
        1 <= i /\ i <= j /\ j <= Len(seq) }

NonDecreasing(s) == 
  \A i \in 1 .. Len(s)-1 : s[i] <= s[i+1]

Sorted(s) == NonDecreasing(s)

\* Multiset of a sequence (as a function from Values to Nat)
Multiset(s) == [v \in Values |-> 
                  Cardinality({ i \in 1..Len(s) : s[i] = v })]

Permutation(s1, s2) == Multiset(s1) = Multiset(s2)

\* Partition operator: all sequences that could result from a valid
\* partition of interval intv with pivot p.
Partition(seq, intv, p) ==
  LET low  == intv[1] IN
  LET high == intv[2] IN
  { s' \in Seq(Values) :
        /\ Len(s') = Len(seq)
        /\ \A i \in 1..Len(seq) :
             (i < low \/ i > high) => s'[i] = seq[i]
        /\ \A i \in low..p :
             \A j \in p+1..high :
               s'[i] <= s'[j]
        /\ Permutation(s', seq) }

\*-----------------------------------------------------------------
\* Variables
\*-----------------------------------------------------------------
VARIABLES seq, orig, work, pc

\*-----------------------------------------------------------------
\* Initial state
\*-----------------------------------------------------------------
Init ==
  /\ seq \in LimitedSeq
  /\ Len(seq) > 0
  /\ orig = seq
  /\ work = { <<1, Len(seq)>> }
  /\ pc = "Loop"

\*-----------------------------------------------------------------
\* Main step
\*-----------------------------------------------------------------
Step1 ==
  /\ work # {}
  /\ LET a   == CHOOSE x \in work : TRUE
         low == a[1]
         high == a[2]
     IN
     /\ IF low = high
        THEN /\ work' = work \ {a}
             /\ seq'  = seq
        ELSE
          /\ \E p \in low .. high :
               LET lower == IF low <= p-1 THEN {<<low, p-1>>} ELSE {}
                   upper == IF p+1 <= high THEN {<<p+1, high>>} ELSE {}
               IN
               /\ \E newSeq \in Partition(seq, a, p) :
                     /\ seq'  = newSeq
                     /\ work' = (work \ {a}) \cup lower \cup upper
     /\ UNCHANGED orig
     /\ pc' = "Loop"

Step2 ==
  /\ work = {}
  /\ pc = "Loop"
  /\ pc' = "Done"
  /\ UNCHANGED <<seq, orig, work>>

StepStutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<seq, orig, work, pc>>

Next == Step1 \/ Step2 \/ StepStutter

\*-----------------------------------------------------------------
\* Specification
\*-----------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\*-----------------------------------------------------------------
\* Type correctness invariant
\*-----------------------------------------------------------------
TypeOK ==
  /\ seq \in LimitedSeq
  /\ orig \in LimitedSeq
  /\ work \subseteq Intervals(seq)

\*-----------------------------------------------------------------
\* Main inductive invariant
\*-----------------------------------------------------------------
Inv ==
  /\ TypeOK
  /\ Permutation(seq, orig)

\*-----------------------------------------------------------------
\* Partial correctness condition (holds at termination)
\*-----------------------------------------------------------------
PCorrect ==
  pc = "Done" => (Sorted(seq) /\ Permutation(seq, orig))

\*-----------------------------------------------------------------
\* Liveness property: eventual termination
\*-----------------------------------------------------------------
Termination == <> (pc = "Done")

\*-----------------------------------------------------------------
\* Declarations required by the .cfg file
\*-----------------------------------------------------------------
THEOREM Spec => []Inv
THEOREM Spec => []PCorrect
THEOREM Spec => [] (TypeOK)
\* The .cfg will refer to the following names directly
CONSTANTS == { Values, MaxSeqLen }
SPECIFICATION == Spec
INVARIANTS == { PCorrect, TypeOK, Inv }
PROPERTIES == { Termination }

====