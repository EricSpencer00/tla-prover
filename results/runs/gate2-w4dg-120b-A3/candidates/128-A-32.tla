---- MODULE Quicksort ----
EXTENDS Naturals, Integers, FiniteSets, Sequences
CONSTANTS Values, MaxSeqLen

VARIABLES seq, origSeq, todo, pc
vars == <<seq, origSeq, todo, pc>>
Intervals == [from: 1..MaxSeqLen, to: 1..MaxSeqLen]
Singleton(a) == [from |-> a, to |-> a]

TypeOK ==
  /\ seq \in Seq(Values)
  /\ Len(seq) <= MaxSeqLen
  /\ origSeq \in Seq(Values)
  /\ Len(origSeq) <= MaxSeqLen
  /\ todo \subseteq Intervals
  /\ pc \in {"run", "done"}

\* Partition(q, i) is the set of sequences produced by a partition of q over
\* some interval and pivot: elements outside the interval are unchanged, and
\* every element at or below the pivot index is <= every element above.
Partition(q, i) ==
  { r \in Seq(Values) :
       /\ Len(r) = Len(q)
       /\ \A k \in 1..Len(q) : k < i => r[k] <= r[i]
       /\ \A k \in 1..Len(q) : k > i => r[i] <= r[k]
       /\ \A k \in 1..Len(q) : (k < i \/ k > i) => r[k] = q[k] }

Init ==
  /\ \E q \in Seq(Values) :
       /\ Len(q) > 0
       /\ seq = q
       /\ origSeq = q
  /\ todo = { [from |-> 1, to |-> Len(seq)] }
  /\ pc = "run"

\* One iteration of the quicksort loop: partition an interval or drop a
\* singleton. The work set shrinks and the sequence changes together.
Step ==
  /\ pc = "run"
  /\ \E i \in todo :
       IF i.from = i.to
         THEN todo' = todo \ {i}
         ELSE
           /\ \E p \in i.from..i.to : seq' \in Partition(seq, p)
           /\ todo' = (todo \ {i}) \cup { [from |-> i.from, to |-> p], [from |-> p + 1, to |-> i.to] }
  /\ pc' = "run"

Terminate ==
  /\ pc = "run"
  /\ todo = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, origSeq, todo>>

Idle == pc = "done" /\ UNCHANGED vars
Next == Step \/ Terminate \/ Idle

Spec == Init /\ [][Next]_vars /\ WF_vars(Step) /\ WF_vars(Terminate)

\* The run-time partitioning is never allowed to change the multiset of
\* elements; the final result must be a permutation of the input.
Permutation ==
  {[i \in 1..Len(seq) |-> origSeq[i]] : i \in 1..Len(seq)} =
   {[i \in 1..Len(seq) |-> seq[i]] : i \in 1..Len(seq)}

DomainPartitioned ==
  /\ \A a, b \in 1..Len(seq) : a <= b => seq[a] <= seq[b]
  /\ \A a, b \in 1..Len(seq) : a > b => seq[b] <= seq[a]

PCorrect == (pc = "done") => Permutation
Inv == Permutation /\ DomainPartitioned

Termination == pc = "done"
====