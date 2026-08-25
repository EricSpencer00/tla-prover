---- MODULE Quicksort ----
EXTENDS Sequences, Naturals, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen

\* ---------- Helper definitions ----------
LimitedSeq ==
  { s \in Seq(Values) : Len(s) > 0 /\ Len(s) <= MaxSeqLen }

Count(seq, v) ==
  Cardinality({ i \in DOMAIN seq : seq[i] = v })

Permutation(s1, s2) ==
  \A v \in Values : Count(s1, v) = Count(s2, v)

Sorted(seq) ==
  \A i, j \in DOMAIN seq : i < j => seq[i] <= seq[j]

IsInterval(int, seq) ==
  LET l == int[1] IN
  LET h == int[2] IN
    1 <= l /\ l <= h /\ h <= Len(seq)

\* ---------- Variables ----------
VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

\* ---------- Type correctness ----------
TypeOK ==
  /\ seq \in Seq(Values)
  /\ orig \in Seq(Values)
  /\ work \subseteq { int \in (Nat \X Nat) : IsInterval(int, seq) }
  /\ pc \in {"Run", "Done"}

\* ---------- Invariant ----------
Inv ==
  /\ TypeOK
  /\ Permutation(seq, orig)

\* ---------- Initial state ----------
Init ==
  /\ seq \in LimitedSeq
  /\ orig = seq
  /\ work = { <<1, Len(seq)>> }
  /\ pc = "Run"

\* ---------- Next-state relation ----------
Next ==
  \/ /\ pc = "Run"
     /\ work # {}
     /\ \E int \in work :
          LET l == int[1] IN
          LET h == int[2] IN
          IF l = h THEN
            /\ work' = work \ {int}
            /\ UNCHANGED <<seq, orig, pc>>
          ELSE
            /\ \E pivot \in l .. h :
                 /\ \E newSeq \in Seq(Values) :
                      /\ Len(newSeq) = Len(seq)
                      /\ (\A i \in DOMAIN seq :
                           IF i < l \/ i > h
                           THEN newSeq[i] = seq[i]
                           ELSE TRUE)
                      /\ (\A i \in l .. pivot :
                           \A j \in pivot+1 .. h :
                              newSeq[i] <= newSeq[j])
                      /\ Permutation(seq, newSeq)
                      /\ seq' = newSeq
                      /\ work' = (work \ {int}) \cup { <<l, pivot>>, <<pivot+1, h>> }
                      /\ pc' = "Run"
  \/ /\ pc = "Run"
     /\ work = {}
     /\ pc' = "Done"
     /\ UNCHANGED <<seq, orig, work>>
  \/ /\ pc = "Done"
     /\ UNCHANGED <<seq, orig, work, pc>>

\* ---------- Specification ----------
Spec == Init /\ [][Next]_vars

\* ---------- Partial correctness property ----------
PCorrect ==
  (pc = "Done" /\ work = {}) => (Sorted(seq) /\ Permutation(seq, orig))

\* ---------- Liveness (termination) ----------
Termination == []<>(pc = "Done")

====