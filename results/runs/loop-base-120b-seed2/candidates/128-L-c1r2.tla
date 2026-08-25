---- MODULE Quicksort ----
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

\*-----------------------------------------------------------------
\* Constants required by the .cfg file
\*-----------------------------------------------------------------
CONSTANTS Values, MaxSeqLen

\*-----------------------------------------------------------------
\* Helper operator: a finite version of Seq bounded by MaxSeqLen
\*-----------------------------------------------------------------
LimitedSeq(V) == { s \in Seq(V) : Len(s) <= MaxSeqLen }

\*-----------------------------------------------------------------
\* State variables
\*-----------------------------------------------------------------
VARIABLES seq, orig, work, pc

\*-----------------------------------------------------------------
\* Types and basic predicates
\*-----------------------------------------------------------------
\* An interval is a pair <<lo,hi>> with 1 ≤ lo ≤ hi ≤ Len(seq)
IsInterval(intv) ==
    /\ intv \in Seq(Nat) /\ Len(intv) = 2
    /\ LET lo == intv[1] IN
       LET hi == intv[2] IN
          /\ 1 <= lo /\ lo <= hi /\ hi <= Len(seq)

\* Sortedness of a sequence
Sorted(s) ==
    /\ Len(s) >= 0
    /\ \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

\* Equality of multisets of two sequences (permutation)
Perm(s1, s2) ==
    /\ Len(s1) = Len(s2)
    /\ \A v \in Values :
          Cardinality({ i \in 1..Len(s1) : s1[i] = v }) =
          Cardinality({ i \in 1..Len(s2) : s2[i] = v })

\* Count of a value inside a sub‑range of a sequence
CountIn(s, lo, hi, v) ==
    Cardinality({ i \in lo..hi : s[i] = v })

\* Predicate expressing that newSeq is a legal partition of oldSeq
\* over interval [lo..hi] with pivot p
Partition(oldSeq, newSeq, lo, hi, p) ==
    /\ Len(newSeq) = Len(oldSeq)
    /\ \A i \in 1..Len(oldSeq) :
         IF i \notin lo..hi
         THEN newSeq[i] = oldSeq[i]
         ELSE TRUE
    /\ \A i \in lo..p, j \in p+1..hi : newSeq[i] <= newSeq[j]
    /\ \A v \in Values :
         CountIn(oldSeq, lo, hi, v) = CountIn(newSeq, lo, hi, v)

\*-----------------------------------------------------------------
\* Initial state
\*-----------------------------------------------------------------
Init ==
    /\ seq \in LimitedSeq(Values) /\ Len(seq) > 0
    /\ orig = seq
    /\ work = { <<1, Len(seq)>> }
    /\ pc = "Loop"

\*-----------------------------------------------------------------
\* Next-state relation
\*-----------------------------------------------------------------
Next ==
    \/ (* main loop step when work is non‑empty *)
       /\ pc = "Loop"
       /\ work # {}
       /\ LET intv == CHOOSE i \in work : TRUE
          IN
          LET lo == intv[1]
              hi == intv[2]
          IN
          IF lo = hi THEN
              /\ work' = work \ {intv}
              /\ UNCHANGED <<seq, orig, pc>>
          ELSE
              /\ \E p \in lo..hi :
                    \E newSeq \in Seq(Values) :
                       /\ Len(newSeq) = Len(seq)
                       /\ Partition(seq, newSeq, lo, hi, p)
                       /\ LET lower == IF lo <= p-1 THEN { <<lo, p-1>> } ELSE {}
                              upper == IF p+1 <= hi THEN { <<p+1, hi>> } ELSE {}
                              newWork == (work \ {intv}) \cup lower \cup upper
                          IN
                          /\ seq' = newSeq
                          /\ work' = newWork
                          /\ UNCHANGED orig
              /\ pc' = "Loop"
    \/ (* termination step *)
       /\ pc = "Loop"
       /\ work = {}
       /\ pc' = "Done"
       /\ UNCHANGED <<seq, orig, work>>
    \/ (* stuttering after termination *)
       /\ pc = "Done"
       /\ UNCHANGED <<seq, orig, work, pc>>

\*-----------------------------------------------------------------
\* Specification
\*-----------------------------------------------------------------
vars == <<seq, orig, work, pc>>
Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

\*-----------------------------------------------------------------
\* Invariants
\*-----------------------------------------------------------------
TypeOK ==
    /\ Values \subseteq Int
    /\ MaxSeqLen \in Nat
    /\ seq \in LimitedSeq(Values)
    /\ orig \in LimitedSeq(Values)
    /\ work \subseteq { intv \in Seq(Nat) : Len(intv) = 2 }
    /\ \A intv \in work : IsInterval(intv)
    /\ pc \in {"Loop", "Done"}

Inv ==
    /\ TypeOK
    /\ \A intv \in work :
          LET lo == intv[1] IN LET hi == intv[2] IN
          /\ 1 <= lo /\ lo <= hi /\ hi <= Len(seq)

PCorrect ==
    (pc = "Done") => /\ Perm(seq, orig) /\ Sorted(seq)

\*-----------------------------------------------------------------
\* Liveness property: termination
\*-----------------------------------------------------------------
Termination == <> (pc = "Done")

\*-----------------------------------------------------------------
\* Exported identifiers required by the .cfg file
\*-----------------------------------------------------------------
SPECIFICATION == Spec
INVARIANTS == {PCorrect, TypeOK, Inv}
PROPERTIES == {Termination}
====