---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen

\* ---------- Helper definitions ----------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

Count(s, v) == Cardinality({ i \in 1..Len(s) : s[i] = v })

Permutation(s, t) == 
  /\ Len(s) = Len(t)
  /\ \A v \in Values : Count(s, v) = Count(t, v)

Interval == <<i, j>>  \* tuple of two indices

IntervalSet(seq) == { <<i, j>> : i \in 1..Len(seq), j \in i..Len(seq) }

NewIntervals(I, p) == 
  LET i == I[1], j == I[2] IN
    { <<i, p>> } \cup
    (IF p + 1 <= j THEN { <<p + 1, j>> } ELSE {})

Partition(oldSeq, I, p) == 
  { newSeq \in LimitedSeq(Values) :
      /\ Len(newSeq) = Len(oldSeq)
      /\ \A k \in 1..Len(oldSeq) :
           (k \notin I[1]..I[2]) => newSeq[k] = oldSeq[k]
      /\ \A a \in I[1]..p :
           \A b \in p+1..I[2] :
               newSeq[a] <= newSeq[b] }

\* ---------- Variables ----------
VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

\* ---------- Initial state ----------
Init == 
  /\ seq \in LimitedSeq(Values) /\ Len(seq) > 0
  /\ orig = seq
  /\ work = { <<1, Len(seq)>> }
  /\ pc = "Run"

\* ---------- Next-state relation ----------
ProcessSingleton ==
  /\ pc = "Run"
  /\ work # {}
  /\ \E I \in work :
        /\ I[1] = I[2]               \* singleton interval
        /\ seq' = seq
        /\ orig' = orig
        /\ work' = work \ {I}
        /\ pc' = "Run"

ProcessPartition ==
  /\ pc = "Run"
  /\ work # {}
  /\ \E I \in work :
        /\ I[1] < I[2]                 \* non‑singleton
        /\ \E p \in I[1]..I[2] :
              /\ seq' \in Partition(seq, I, p)
              /\ work' = (work \ {I}) \cup NewIntervals(I, p)
              /\ orig' = orig
              /\ pc' = "Run"

Terminate ==
  /\ pc = "Run"
  /\ work = {}
  /\ pc' = "Done"
  /\ UNCHANGED <<seq, orig, work>>

StutterAfterDone ==
  /\ pc = "Done"
  /\ UNCHANGED <<seq, orig, work, pc>>

Next == 
  \/ ProcessSingleton
  \/ ProcessPartition
  \/ Terminate
  \/ StutterAfterDone

\* ---------- Specification ----------
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ---------- Type correctness ----------
TypeOK == 
  /\ seq \in LimitedSeq(Values)
  /\ orig \in LimitedSeq(Values)
  /\ Len(orig) = Len(seq)
  /\ work \subseteq IntervalSet(seq)
  /\ pc \in {"Run", "Done"}

\* ---------- Invariant ----------
Inv == Permutation(seq, orig)

\* ---------- Program‑counter correctness ----------
PCorrect == (pc = "Done") => (work = {})

\* ---------- Liveness property ----------
Termination == <> (pc = "Done")

====