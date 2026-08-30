---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

VARIABLES seq, orig, work, pc
vars == <<seq, orig, work, pc>>

Intervals == {p \in (1..(MaxSeqLen + 1)) \X (1..(MaxSeqLen + 1)) : p[1] <= p[2]}
\* The interval is inclusive on both ends, so a singleton is a pair of equal indices.
Singleton(i) == <<i, i>>
Range(i) == i[2] - i[1] + 1
Domain == 1..MaxSeqLen
SubSequences(s) == {p \in Sequences.Seq(Domain) : \A i \in DOMAIN p : p[i] \in s}
\* A partition moves values between the two subintervals but never introduces or deletes any.
Partitions(v, i, k) ==
  {w \in SubSequences(v) :
     /\ (\A i \in DOMAIN w : (i \notin i) => w[i] = v[i])
     /\ (\A i \in DOMAIN w : i \in i => w[i] <= w[k])
     /\ (\A i \in DOMAIN w : i \in i => w[k] <= w[i])}

TypeOK ==
  /\ seq \in SubSequences(Values)
  /\ orig \in SubSequences(Values)
  /\ work \in SUBSET Intervals
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E s \in {p \in SubSequences(Values) : Len(p) >= 1} : seq = s
  /\ orig = seq
  /\ work = {Singleton(1)}
  /\ pc = "loop"

PCorrect == (pc = "done") => (work = {})

\* The partition is nondeterministic, so the sortedness argument needs both
\* partition properties plus the reduction of the work set.
Inv ==
  /\ work \subseteq Intervals
  /\ \A i \in work : i[2] <= Len(seq)
  /\ \A i \in work : (Range(i) >= 2) => (\E k \in i[1]..i[2] : seq[i[1]..i[2]] \in Partitions(seq[i[1]..i[2]], i, k)
  /\ Seq(orig) = Seq(seq)
  /\ (\A i, j \in work : (i[2] < j[2] /\ j[1] <= i[2]) => seq[i[2]] <= seq[j[1]])

\* The subintervals always partition the original interval, so the reduction
\* of work is bounded by the original length, not by the values themselves.
Stall == (pc = "done") /\ UNCHANGED vars
Next ==
  \/ \E i \in work :
       /\ i \in work
       /\ (Range(i) = 1 \/ \E k \in i[1]..i[2] : seq[i[1]..i[2]] \in Partitions(seq[i[1]..i[2]], i, k))
       /\ work' = (work \ {i}) \cup IF Range(i) <= 1 THEN {} ELSE {<<i[1], i[2] - 1>>, <<i[2], i[2>>}
       /\ UNCHANGED <<seq, orig>>
  \/ (pc = "loop" /\ work = {})
       /\ pc' = "done"
       /\ UNCHANGED <<seq, orig, work>>
  \/ Stall

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

\* Each partition splits one more interval, so the number of intervals is capped
\* by the original length and weak fairness closes out the run.
Termination == []<> (pc = "done")
====