---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

Count(seq, v) ==
  Cardinality({ i \in DOMAIN seq : seq[i] = v })

Permutes(s1, s2) ==
  /\ Len(s1) = Len(s2)
  /\ \A v \in Values : Count(s1, v) = Count(s2, v)

Sorted(seq) ==
  \A i, j \in DOMAIN seq : i < j => seq[i] <= seq[j]

\* An interval is a pair <<lo, hi>> with 1 <= lo <= hi
Interval == <<Nat, Nat>>

Lower(i) == i[1]
Upper(i) == i[2]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Type correctness
\* ----------------------------------------------------------------------
TypeOK ==
  /\ seq \in LimitedSeq(Values)
  /\ orig \in LimitedSeq(Values)
  /\ work \subseteq { <<l, h>> \in Interval :
                     1 <= l /\ l <= h /\ h <= Len(seq) }
  /\ pc \in {"Loop", "Done"}

\* ----------------------------------------------------------------------
\* Invariant relating current sequence to original
\* ----------------------------------------------------------------------
Inv == /\ TypeOK
       /\ Permutes(seq, orig)

\* ----------------------------------------------------------------------
\* PCorrect: when the algorithm has finished the work set is empty
\* ----------------------------------------------------------------------
PCorrect == (pc = "Done") => (work = {})

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ seq \in LimitedSeq(Values) \setminus {<<>>}
  /\ orig = seq
  /\ work = { <<1, Len(seq)>> }
  /\ pc = "Loop"

\* ----------------------------------------------------------------------
\* Partition predicate (abstract)
\* ----------------------------------------------------------------------
Partition(old, new, lo, hi, p) ==
  /\ \A i \in DOMAIN old :
        (i < lo \/ i > hi) => new[i] = old[i]
  /\ \A i \in lo..p :
        \A j \in p+1..hi :
          new[i] <= new[j]
  /\ Permutes(SubSeq(old, lo, hi), SubSeq(new, lo, hi))

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ /\ pc = "Loop"
     /\ work # {}
     /\ \E I \in work :
          LET l == Lower(I) IN
          LET h == Upper(I) IN
          IF l = h THEN
            /\ work' = work \ {I}
            /\ seq' = seq
            /\ orig' = orig
            /\ pc' = "Loop"
          ELSE
            /\ \E p \in l..h :
                 /\ \E newSeq \in LimitedSeq(Values) :
                      /\ Len(newSeq) = Len(seq)
                      /\ Partition(seq, newSeq, l, h, p)
            /\ seq' = newSeq
            /\ orig' = orig
            /\ work' = (work \ {I}) \cup
                       {<<l, p-1>> : l <= p-1} \cup
                       {<<p+1, h>> : p+1 <= h}
            /\ pc' = "Loop"
  \/ /\ pc = "Loop"
     /\ work = {}
     /\ pc' = "Done"
     /\ UNCHANGED <<seq, orig, work>>
  \/ /\ pc = "Done"
     /\ UNCHANGED vars

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Liveness property: termination
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

=============================================================================