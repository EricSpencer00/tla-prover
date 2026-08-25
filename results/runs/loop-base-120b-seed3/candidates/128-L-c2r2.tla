---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* Finite version of Seq for model checking
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\* ----------------------------------------------------------------------
\* State variables
VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Helper definitions
IsSorted(s) ==
  \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

Permutation(s1, s2) ==
  /\ Len(s1) = Len(s2)
  /\ \A v \in Values :
        Cardinality({ i \in 1..Len(s1) : s1[i] = v }) =
        Cardinality({ i \in 1..Len(s2) : s2[i] = v })

\* intervals are represented as 2‑tuples <<low,high>>
ValidInterval(iv) ==
  /\ iv \in Nat \X Nat
  /\ iv[1] <= iv[2]

\* ----------------------------------------------------------------------
\* Initial state
Init ==
  /\ seq \in LimitedSeq(Values)
  /\ Len(seq) > 0
  /\ orig = seq
  /\ work = { <<1, Len(seq)>> }
  /\ pc = "Run"

\* ----------------------------------------------------------------------
\* Transition relation
Next ==
  \/ /\ pc = "Run"
     /\ work # {}
     /\ \E iv \in work :
          /\ iv[1] = iv[2]            \* singleton interval
          /\ seq' = seq
          /\ orig' = orig
          /\ work' = work \ {iv}
          /\ pc' = "Run"

  \/ /\ pc = "Run"
     /\ work # {}
     /\ \E iv \in work :
          /\ iv[1] < iv[2]            \* interval with >1 element
          /\ \E p \in iv[1] .. iv[2] :
               LET low   == iv[1],
                   high  == iv[2],
                   lower == IF low <= p-1 THEN { <<low, p-1>> } ELSE {},
                   upper == IF p+1 <= high THEN { <<p+1, high>> } ELSE {},
                   newSeq == CHOOSE ns \in LimitedSeq(Values) :
                               /\ Len(ns) = Len(seq)
                               /\ \A i \in 1..Len(seq) :
                                    (i < low \/ i > high) => ns[i] = seq[i]
                               /\ \A i \in low..p : \A j \in p+1..high : ns[i] <= ns[j]
                               /\ \A v \in Values :
                                    Cardinality({ i \in low..high : ns[i] = v }) =
                                    Cardinality({ i \in low..high : seq[i] = v })
               IN /\ seq' = newSeq
                  /\ orig' = orig
                  /\ work' = (work \ {iv}) \cup lower \cup upper
                  /\ pc' = "Run"

  \/ /\ pc = "Run"
     /\ work = {}
     /\ pc' = "Done"
     /\ UNCHANGED <<seq, orig, work>>

  \/ /\ pc = "Done"
     /\ UNCHANGED vars

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
TypeOK ==
  /\ seq \in LimitedSeq(Values)
  /\ orig \in LimitedSeq(Values)
  /\ Len(seq) = Len(orig)
  /\ work \subseteq Nat \X Nat
  /\ \A iv \in work : ValidInterval(iv)
  /\ pc \in {"Run", "Done"}

Inv ==
  /\ Permutation(seq, orig)
  /\ \A iv \in work : ValidInterval(iv)

PCorrect ==
  (pc = "Done") => (IsSorted(seq) /\ Permutation(seq, orig))

\* ----------------------------------------------------------------------
\* Liveness property
Termination == <> (pc = "Done")

\* ----------------------------------------------------------------------
\* Exported identifiers required by the .cfg file
SPECIFICATION Spec
INVARIANTS TypeOK, Inv, PCorrect
PROPERTIES Termination
====