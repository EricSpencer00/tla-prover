---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen

\* ---------- Helper definitions ----------
\* Bounded version of Seq
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\* An interval is a pair <<low,high>> with low <= high
Interval == <<low : Nat, high : Nat>>

\* Set of all intervals that fit inside the current sequence
ALLINTERVALS(seq) == { <<l, h>> \in Interval :
                        l \in 1..Len(seq) /\ h \in l..Len(seq) }

\* Permutation of two sequences (same length, bijective rearrangement)
IsPermutation(s, t) ==
  /\ Len(s) = Len(t)
  /\ \E f \in [1..Len(s) -> 1..Len(s)] :
        (\A i,j \in 1..Len(s) : f[i] = f[j] => i = j) /\    \* f is injective, hence bijective
        t = [i \in 1..Len(t) |-> s[f[i]]]

\* Partition property for a given interval I = <<l,h>> and pivot p
PartitionOK(old, new, I, p) ==
  LET l == I[1] IN
  LET h == I[2] IN
  /\ \A i \in 1..Len(old) : (i < l) \/ (i > h) => new[i] = old[i]
  /\ \A i \in l..p : \A j \in (p+1)..h : new[i] <= new[j]

\* ---------- Variables ----------
VARIABLES seq, origSeq, work, pc

\* ---------- Initial state ----------
Init ==
  \E initSeq \in LimitedSeq(Values) :
    /\ Len(initSeq) > 0
    /\ seq = initSeq
    /\ origSeq = initSeq
    /\ work = { <<1, Len(initSeq)>> }
    /\ pc   = "Loop"

\* ---------- Next-state relation ----------
Next ==
  \/ /\ pc = "Loop"
     /\ work # {}
     /\ \E I \in work :
          LET l == I[1] IN
          LET h == I[2] IN
          IF l = h THEN
            /\ work' = (work \ {I})
            /\ UNCHANGED <<seq, origSeq, pc>>
          ELSE
            /\ \E p \in l..h :
                 /\ \E newSeq \in LimitedSeq(Values) :
                      /\ Len(newSeq) = Len(seq)
                      /\ IsPermutation(seq, newSeq)
                      /\ PartitionOK(seq, newSeq, I, p)
                 /\ seq'   = newSeq
                 /\ origSeq' = origSeq
                 /\ work' = (work \ {I}) \cup
                            { <<l, p>>, <<p+1, h>> }
                 /\ pc'   = "Loop"
  \/ /\ pc = "Loop"
     /\ work = {}
     /\ pc' = "Done"
     /\ UNCHANGED <<seq, origSeq, work>>
  \/ /\ pc = "Done"
     /\ UNCHANGED <<seq, origSeq, work, pc>>

\* ---------- Specification ----------
Spec == Init /\ [][Next]_<<seq, origSeq, work, pc>>

\* ---------- Invariant definitions ----------
PCorrect == (pc = "Done") => (work = {})

TypeOK ==
  /\ seq \in LimitedSeq(Values)
  /\ origSeq \in LimitedSeq(Values)
  /\ Len(seq) = Len(origSeq)
  /\ work \subseteq ALLINTERVALS(seq)
  /\ pc \in {"Loop", "Done"}

\* Elements that are not inside any pending interval must be locally sorted
SortedOutsideWork ==
  \A i \in 1..Len(seq)-1 :
    (\A I \in work : ~(i \in I[1]..I[2] /\ i+1 \in I[1]..I[2]))
    => seq[i] <= seq[i+1]

Inv ==
  /\ IsPermutation(seq, origSeq)
  /\ SortedOutsideWork

\* ---------- Temporal properties ----------
Termination == <> (pc = "Done")

\* ---------- Theorem (partial correctness) ----------
THEOREM Spec => [] (PCorrect /\ TypeOK /\ Inv)

====