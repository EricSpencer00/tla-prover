---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* Finite version of Seq for model checking
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\* ----------------------------------------------------------------------
\* State variables
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Types
Interval == [low : Nat, high : Nat]

IsInterval(I) ==
  /\ I.low \in Nat
  /\ I.high \in Nat
  /\ I.low <= I.high
  /\ I.high <= Len(seq)

\* ----------------------------------------------------------------------
\* Helper predicates
IsSorted(s) ==
  \A i, j \in DOMAIN(s) : i < j => s[i] <= s[j]

Permutation(s1, s2) ==
  \A v \in Values :
    Cardinality({ i \in DOMAIN(s1) : s1[i] = v }) =
    Cardinality({ i \in DOMAIN(s2) : s2[i] = v })

\* ----------------------------------------------------------------------
\* Initial state
Init ==
  /\ seq \in LimitedSeq(Values)
  /\ Len(seq) > 0
  /\ orig = seq
  /\ work = { [low |-> 1, high |-> Len(seq)] }
  /\ pc = "Loop"

\* ----------------------------------------------------------------------
\* Actions

\* Termination detection
Terminate ==
  /\ pc = "Loop"
  /\ work = {}
  /\ pc' = "Done"
  /\ UNCHANGED << seq, orig, work >>

\* Remove a singleton interval
RemoveSingleton ==
  \E I \in work :
    /\ I.low = I.high
    /\ work' = work \ {I}
    /\ UNCHANGED << seq, orig >>
    /\ pc' = "Loop"

\* Partition step on a non‑singleton interval
PartitionStep ==
  \E I \in work :
    LET l == I.low
        h == I.high IN
    /\ l < h
    /\ \E p \in l..h :
        \E newSeq \in LimitedSeq(Values) :
          /\ ( \A i \in DOMAIN(seq) :
                (i < l \/ i > h) => newSeq[i] = seq[i] )
          /\ ( \A i \in l..p, j \in p+1..h :
                newSeq[i] <= newSeq[j] )
          /\ Permutation(newSeq, seq)
          /\ seq' = newSeq
    /\ work' = (work \ {I}) \cup {
                [low |-> l, high |-> p],
                [low |-> p+1, high |-> h]
              }
    /\ UNCHANGED orig
    /\ pc' = "Loop"

\* Stuttering after termination
StutterDone ==
  /\ pc = "Done"
  /\ UNCHANGED << seq, orig, work, pc >>

Next ==
  \/ Terminate
  \/ RemoveSingleton
  \/ PartitionStep
  \/ StutterDone

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Invariants
TypeOK ==
  /\ seq \in LimitedSeq(Values)
  /\ orig \in LimitedSeq(Values)
  /\ work \subseteq { I \in Interval : IsInterval(I) }
  /\ pc \in {"Loop", "Done"}

Inv == TypeOK /\ Permutation(seq, orig)

PCorrect ==
  (pc = "Done") => (IsSorted(seq) /\ Permutation(seq, orig))

\* ----------------------------------------------------------------------
\* Liveness property
Termination == <> (pc = "Done")

\* ----------------------------------------------------------------------
\* Exported identifiers required by the .cfg file
SPECIFICATION Spec
INVARIANT PCorrect
INVARIANT TypeOK
INVARIANT Inv
PROPERTY Termination

====