---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, Integers

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\*  Finite version of Seq, to be used by the model checker (replaces Seq)
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\* ----------------------------------------------------------------------
\*  State variables
\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\*  Helper definitions
\* ----------------------------------------------------------------------
InterLow(i)  == i[1]
InterHigh(i) == i[2]
InterIndices(i) == InterLow(i) .. InterHigh(i)

CountInInterval(s, inter, v) ==
  Cardinality({ i \in InterIndices(inter) : s[i] = v })

\* Permutation of whole sequences (multiset equality)
Permutes(s1, s2) ==
  /\ Len(s1) = Len(s2)
  /\ \A v \in Values :
        Cardinality({ i \in 1..Len(s1) : s1[i] = v })
        =
        Cardinality({ i \in 1..Len(s2) : s2[i] = v })

\* Sortedness of a sequence (non‑decreasing order)
Sorted(s) ==
  \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

\* PartitionResult captures any valid partition result for a given interval
PartitionResult(s, inter, piv) ==
  { s2 \in LimitedSeq(Values) :
      /\ Len(s2) = Len(s)
      /\ \A i \in 1..Len(s) :
            (i \notin InterIndices(inter)) => s2[i] = s[i]
      /\ \A i, j \in InterIndices(inter) :
            (i <= piv /\ j > piv) => s2[i] <= s2[j]
      /\ \A v \in Values :
            CountInInterval(s, inter, v) = CountInInterval(s2, inter, v) }

\* ----------------------------------------------------------------------
\*  Type correctness
\* ----------------------------------------------------------------------
TypeOK ==
  /\ seq \in LimitedSeq(Values)
  /\ orig \in LimitedSeq(Values)
  /\ Len(seq) = Len(orig)
  /\ Len(seq) > 0
  /\ work \subseteq { <<l, h>> : l \in 1..Len(seq) /\ h \in l..Len(seq) }
  /\ pc \in {"Loop", "Done"}

\* ----------------------------------------------------------------------
\*  Invariant (preserves permutation and well‑formed intervals)
\* ----------------------------------------------------------------------
Inv == /\ TypeOK
       /\ Permutes(seq, orig)

\* ----------------------------------------------------------------------
\*  Partial‑correctness condition (holds when algorithm finishes)
\* ----------------------------------------------------------------------
PCorrect ==
  (pc = "Done") => /\ Sorted(seq)
                  /\ Permutes(seq, orig)

\* ----------------------------------------------------------------------
\*  Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ seq \in LimitedSeq(Values)
  /\ Len(seq) > 0
  /\ orig = seq
  /\ work = { <<1, Len(seq)>> }
  /\ pc = "Loop"

\* ----------------------------------------------------------------------
\*  Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ /\ pc = "Loop"
     /\ work # {}
     /\ \E inter \in work :
          LET l == InterLow(inter) IN
          LET h == InterHigh(inter) IN
          IF l = h THEN
            /\ work' = work \ {inter}
            /\ UNCHANGED <<seq, orig, pc>>
          ELSE
            \E piv \in l..h :
              LET newSeq \in PartitionResult(seq, inter, piv) IN
                /\ seq' = newSeq
                /\ work' = (work \ {inter}) \cup
                           { <<l, piv-1>>, <<piv+1, h>> }
                /\ UNCHANGED orig
                /\ pc' = pc
  \/ /\ pc = "Loop"
     /\ work = {}
     /\ pc' = "Done"
     /\ UNCHANGED <<seq, orig, work>>
  \/ /\ pc = "Done"
     /\ UNCHANGED <<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\*  Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\*  Liveness property: termination
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

=============================================================================