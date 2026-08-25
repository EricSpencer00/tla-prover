---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen

\* -------------------------------------------------
\* Types
\* -------------------------------------------------
\* A finite sequence of values, length bounded by MaxSeqLen
LimitedSeq ==
  { s \in Seq :
      Len(s) <= MaxSeqLen /\ 
      \A i \in 1..Len(s) : s[i] \in Values }

\* An interval is a pair <<low, high>> with low <= high
Interval == <<Nat, Nat>>

\* -------------------------------------------------
\* Variables
\* -------------------------------------------------
VARIABLES seq, orig, work, pc
vars == <<seq, orig, work, pc>>

\* -------------------------------------------------
\* Helper definitions
\* -------------------------------------------------
Count(s, v) ==
  Cardinality({ i \in 1..Len(s) : s[i] = v })

Permutation(s1, s2) ==
  /\ Len(s1) = Len(s2)
  /\ \A v \in Values : Count(s1, v) = Count(s2, v)

Sorted(s) ==
  \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

IntervalCount(s, a, b, v) ==
  Cardinality({ i \in a..b : s[i] = v })

\* Partition returns all sequences that could result from a
\* correct partition of the interval iv around pivot p
Partition(seq, iv, p) ==
  { newSeq \in Seq :
      /\ Len(newSeq) = Len(seq)
      /\ \A i \in 1..Len(seq) :
            (i < iv[1] \/ i > iv[2]) => newSeq[i] = seq[i]
      /\ \A v \in Values :
            IntervalCount(seq, iv[1], iv[2], v) =
            IntervalCount(newSeq, iv[1], iv[2], v)
      /\ \A i \in iv[1]..p :
            \A j \in p+1..iv[2] :
               newSeq[i] <= newSeq[j] }

\* -------------------------------------------------
\* Initial state
\* -------------------------------------------------
Init ==
  /\ seq \in LimitedSeq
  /\ Len(seq) > 0
  /\ orig = seq
  /\ work = { <<1, Len(seq)>> }
  /\ pc = "Loop"

\* -------------------------------------------------
\* Actions
\* -------------------------------------------------
RemoveSingleton ==
  /\ pc = "Loop"
  /\ work # {}
  /\ \E iv \in work :
        /\ iv[1] = iv[2]
        /\ work' = work \ {iv}
        /\ UNCHANGED <<seq, orig, pc>>

PartitionStep ==
  /\ pc = "Loop"
  /\ work # {}
  /\ \E iv \in work :
        /\ iv[1] < iv[2]
        /\ \E p \in iv[1]..iv[2] :
              /\ \E newSeq \in Partition(seq, iv, p) :
                    /\ seq' = newSeq
                    /\ work' = (work \ {iv}) \cup { <<iv[1], p>>, <<p+1, iv[2]>> }
                    /\ UNCHANGED <<orig, pc>>

Terminate ==
  /\ pc = "Loop"
  /\ work = {}
  /\ pc' = "Done"
  /\ UNCHANGED <<seq, orig, work>>

Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  \/ RemoveSingleton
  \/ PartitionStep
  \/ Terminate
  \/ Stutter

\* -------------------------------------------------
\* Specification
\* -------------------------------------------------
Spec == Init /\ [][Next]_vars

\* -------------------------------------------------
\* Invariants
\* -------------------------------------------------
TypeOK ==
  /\ seq \in LimitedSeq
  /\ orig \in LimitedSeq
  /\ work \subseteq { iv \in Interval :
                       iv[1] <= iv[2] /\ iv[2] <= Len(seq) }
  /\ pc \in {"Loop", "Done"}

Inv ==
  /\ TypeOK
  /\ Permutation(seq, orig)
  /\ \A iv \in work :
        iv[1] <= iv[2] /\ iv[2] <= Len(seq)

PCorrect ==
  (pc = "Done") => (Sorted(seq) /\ Permutation(seq, orig))

\* -------------------------------------------------
\* Liveness property
\* -------------------------------------------------
Termination == <> (pc = "Done")

\* -------------------------------------------------
\* Exported identifiers (required by the .cfg)
\* -------------------------------------------------
\* SPECIFICATION
\* INVARIANTS
\* PROPERTIES
\* CONSTANTS already declared
\* LimitedSeq defined above
\* -------------------------------------------------
\* End of module
=============================================================================