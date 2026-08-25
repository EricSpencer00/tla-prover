---- MODULE Quicksort ----
EXTENDS Sequences, FiniteSets, Integers, TLC

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\*  A finite version of Seq, used in the model checking configuration.
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\* ----------------------------------------------------------------------
\*  State variables
\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\*  Helper definitions
\* ----------------------------------------------------------------------
Count(seq_, v_) ==
  Cardinality({ i \in DOMAIN(seq_) : seq_[i] = v_ })

SameBag(seq1, seq2) ==
  \A v \in Values : Count(seq1, v) = Count(seq2, v)

Interval == [low : Nat, high : Nat]

ValidInterval(iv) ==
  /\ iv.low <= iv.high
  /\ iv.low >= 1
  /\ iv.high <= Len(seq)

\* ----------------------------------------------------------------------
\*  Partition operator: all sequences that respect the pivot ordering,
\*  leave elements outside the interval unchanged and preserve the multiset
\*  of the interval.
\* ----------------------------------------------------------------------
Partition(s, iv, piv) ==
  { s_ \in LimitedSeq(Values) :
      /\ Len(s_) = Len(s)
      /\ \A j \in 1..Len(s_) :
           (j < iv.low) \/ (j > iv.high) => s_[j] = s[j]
      /\ SameBag( SubSeq(s, iv.low, iv.high) ,
                  SubSeq(s_, iv.low, iv.high) )
      /\ \A j \in iv.low..piv :
           \A k \in piv+1..iv.high :
               s_[j] <= s_[k] }

\* ----------------------------------------------------------------------
\*  Initial predicate
\* ----------------------------------------------------------------------
Init ==
  /\ seq \in LimitedSeq(Values) /\ Len(seq) > 0
  /\ orig = seq
  /\ work = { [low |-> 1, high |-> Len(seq)] }
  /\ pc = "Loop"

\* ----------------------------------------------------------------------
\*  The main step of the algorithm
\* ----------------------------------------------------------------------
LoopStep ==
  /\ pc = "Loop"
  /\ work # {}
  /\ \E iv \in work :
        LET piv == CHOOSE p \in iv.low..iv.high :
                 TRUE
        IN
        IF iv.low = iv.high THEN
          /\ work' = work \ {iv}
          /\ UNCHANGED <<seq, orig, pc>>
        ELSE
          /\ piv \in iv.low..iv.high
          /\ \E newSeq \in Partition(seq, iv, piv) :
                /\ seq' = newSeq
                /\ orig' = orig
                /\ work' = (work \ {iv}) \cup
                           (IF iv.low <= piv-1
                               THEN { [low |-> iv.low, high |-> piv-1] }
                               ELSE {}) \cup
                           (IF piv+1 <= iv.high
                               THEN { [low |-> piv+1, high |-> iv.high] }
                               ELSE {})
                /\ pc' = "Loop"
        END

Terminate ==
  /\ pc = "Loop"
  /\ work = {}
  /\ pc' = "Done"
  /\ UNCHANGED <<seq, orig, work>>

StutterDone ==
  /\ pc = "Done"
  /\ UNCHANGED <<seq, orig, work, pc>>

Next == LoopStep \/ Terminate \/ StutterDone

\* ----------------------------------------------------------------------
\*  Specification
\* ----------------------------------------------------------------------
vars == <<seq, orig, work, pc>>
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\*  Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ seq \in LimitedSeq(Values)
  /\ orig \in LimitedSeq(Values)
  /\ Len(seq) = Len(orig)
  /\ work \subseteq { iv \in Interval : ValidInterval(iv) }
  /\ pc \in {"Loop", "Done"}

Inv ==
  /\ TypeOK
  /\ SameBag(seq, orig)

PCorrect ==
  /\ pc = "Done"
  /\ \A i, j \in 1..Len(seq) : i < j => seq[i] <= seq[j]

\* ----------------------------------------------------------------------
\*  Liveness property (termination)
\* ----------------------------------------------------------------------
Termination == []<>(pc = "Done")

====