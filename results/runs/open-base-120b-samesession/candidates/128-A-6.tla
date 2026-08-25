---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\*  A finite version of Seq for model checking
\* ----------------------------------------------------------------------
LimitedSeq(V, L) == 
  { s \in Seq(V) : Len(s) <= L /\ Len(s) > 0 }

\* ----------------------------------------------------------------------
\*  State variables
\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\*  Helper definitions
\* ----------------------------------------------------------------------
INTERVALS(s) == { <<i, j>> : i \in 1..Len(s) /\ j \in i..Len(s) }

IsPermutation(s1, s2) ==
  \A x \in Values :
    Cardinality({ i \in 1..Len(s1) : s1[i] = x }) =
    Cardinality({ i \in 1..Len(s2) : s2[i] = x })

Sorted(s) ==
  \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

SubSeq(s, a, b) == 
  [k \in 1..(b - a + 1) |-> s[a + k - 1]]

Partition(s, int, piv) ==
  { s2 \in Seq(Values) :
      Len(s2) = Len(s) /\ 
      \A i \in 1..Len(s) :
        (i < int[1] \/ i > int[2]) => s2[i] = s[i] /\
      \A i \in int[1]..piv :
        \A j \in piv+1..int[2] :
          s2[i] <= s2[j] /\
      IsPermutation(SubSeq(s, int[1], int[2]), SubSeq(s2, int[1], int[2]))
  }

\* ----------------------------------------------------------------------
\*  Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ seq \in LimitedSeq(Values, MaxSeqLen)
  /\ orig = seq
  /\ work = { <<1, Len(seq)>> }
  /\ pc = "Loop"

\* ----------------------------------------------------------------------
\*  Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ /\ pc = "Loop"
     /\ work # {}
     /\ \E int \in work :
          LET i == int[1] IN
          LET j == int[2] IN
          IF i = j THEN
            /\ work' = work \ {int}
            /\ UNCHANGED <<seq, orig, pc>>
          ELSE
            /\ \E piv \in i..j :
                 LET lower == IF piv > i THEN {<<i, piv-1>>} ELSE {} IN
                 LET upper == IF piv < j THEN {<<piv+1, j>>} ELSE {} IN
                 /\ \E s2 \in Partition(seq, int, piv) :
                       /\ seq' = s2
                       /\ work' = (work \ {int}) \cup lower \cup upper
                       /\ pc' = "Loop"
                       /\ UNCHANGED orig
          END
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
\*  Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ seq \in Seq(Values)
  /\ Len(seq) > 0
  /\ orig = seq
  /\ work \subseteq INTERVALS(seq)
  /\ pc \in {"Loop", "Done"}

Inv ==
  /\ IsPermutation(seq, orig)
  /\ work \subseteq INTERVALS(seq)

PCorrect ==
  pc = "Done" => /\ Sorted(seq) /\ IsPermutation(seq, orig)

\* ----------------------------------------------------------------------
\*  Liveness property (termination)
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

====