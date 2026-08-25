---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

\*--------------------------------------------------------------------
\* Constants
\*--------------------------------------------------------------------
CONSTANTS Values, MaxSeqLen

\*--------------------------------------------------------------------
\* Finite version of Seq (used for model checking)
\*--------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\*--------------------------------------------------------------------
\* State variables
\*--------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\*--------------------------------------------------------------------
\* Types
\*--------------------------------------------------------------------
Interval == [low : Nat, high : Nat]

IntervalSet(L) == { [low |-> i, high |-> j] :
                    i \in 1..L /\ j \in i..L }

\*--------------------------------------------------------------------
\* Helper definitions
\*--------------------------------------------------------------------
Count(s, v) == Cardinality({ i \in 1..Len(s) : s[i] = v })

Permutation(s1, s2) ==
  /\ Len(s1) = Len(s2)
  /\ \A v \in Values : Count(s1, v) = Count(s2, v)

Sorted(s) ==
  \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

\* Partition predicate – abstracts the effect of a partition step
Partition(old, new, I, p) ==
  /\ Len(new) = Len(old)
  /\ \A i \in 1..Len(old) :
        (i < I.low \/ i > I.high) => new[i] = old[i]
  /\ \A i \in I.low..p : \A j \in p+1..I.high : new[i] <= new[j]
  /\ Permutation(old, new)

\*--------------------------------------------------------------------
\* Initial state
\*--------------------------------------------------------------------
Init ==
  /\ seq \in LimitedSeq(Values) /\ Len(seq) > 0
  /\ orig = seq
  /\ work = { [low |-> 1, high |-> Len(seq)] }
  /\ pc = "Run"

\*--------------------------------------------------------------------
\* Main action (one iteration of the algorithm)
\*--------------------------------------------------------------------
RunStep ==
  /\ pc = "Run"
  /\ IF work = {}
     THEN /\ pc' = "Done"
          /\ UNCHANGED <<seq, orig, work>>
     ELSE
       /\ \E I \in work :
            /\ IF I.low = I.high
               THEN /\ seq' = seq
                    /\ orig' = orig
                    /\ work' = work \ {I}
                    /\ pc' = "Run"
               ELSE
                 /\ \E p \in I.low .. I.high :
                      /\ \E newSeq \in LimitedSeq(Values) :
                           /\ Partition(seq, newSeq, I, p)
                           /\ seq' = newSeq
                      /\ orig' = orig
                      /\ pc' = "Run"
                      /\ work' = (work \ {I}) \cup
                                 (IF p > I.low
                                    THEN { [low |-> I.low, high |-> p-1] }
                                    ELSE {}) \cup
                                 (IF p < I.high
                                    THEN { [low |-> p+1, high |-> I.high] }
                                    ELSE {})

\*--------------------------------------------------------------------
\* Stuttering after termination
\*--------------------------------------------------------------------
DoneStep ==
  /\ pc = "Done"
  /\ UNCHANGED <<seq, orig, work, pc>>

Next == RunStep \/ DoneStep

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\*--------------------------------------------------------------------
\* Invariants
\*--------------------------------------------------------------------
PCorrect ==
  (pc = "Done") => work = {}

TypeOK ==
  /\ seq \in LimitedSeq(Values)
  /\ orig \in LimitedSeq(Values)
  /\ Len(seq) = Len(orig)
  /\ work \subseteq IntervalSet(Len(seq))
  /\ pc \in {"Run", "Done"}

Inv ==
  /\ TypeOK
  /\ Permutation(seq, orig)
  /\ (work = {} => Sorted(seq))

\*--------------------------------------------------------------------
\* Liveness property (termination)
\*--------------------------------------------------------------------
Termination == <> (pc = "Done")
====