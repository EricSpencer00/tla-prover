---- MODULE Quicksort ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen, Seq

ASSUME Values \subseteq INTEGER

VARIABLES seq, orig, work, pc
vars == <<seq, orig, work, pc>>

TypeOK ==
  /\ seq \in Seq
  /\ /\ Len(seq) \in 1..MaxSeqLen /\ \A i \in 1..Len(seq) : seq[i] \in Values
  /\ orig \in Seq
  /\ /\ Len(orig) = Len(seq) /\ \A i \in 1..Len(seq) : orig[i] \in Values
  /\ work \subseteq (1..Len(seq) \X (1..Len(seq)))
  /\ pc \in {"run", "term"}

\* Intervals in the work set form a partition of the whole domain.
DomainPartitions ==
  /\ \A a \in work : a[1] <= a[2]
  /\ \A i \in 1..Len(seq) : \E a \in work : i \in a[1]..a[2]
  /\ \A a, b \in work : a # b => (a[2] < b[1] \/ b[2] < a[1])

\* A permutation can be written as composition with a domain automorphism.
Permutation(m, s) ==
  /\ Len(s) = Len(seq) /\ \A i \in 1..Len(seq) : s[i] \in Values
  /\ \E f \in [1..Len(seq) -> 1..Len(seq)] :
       /\ \A a, b \in 1..Len(seq) : a = b => f[a] = f[b]
       /\ \A k \in 1..Len(seq) : s[k] = m[f[k]]

SortedWithinInterval(a) ==
  /\ a[1] <= a[2]
  /\ \A i \in a[1]..(a[2] - 1) : seq[i] <= seq[i + 1]

\* A partition keeps everything outside the interval fixed and
\* enforces the pivot ordering inside it.
RelativeSortedness ==
  /\ \A a \in work : SortedWithinInterval(a)
  /\ \A a \in work : a[1] < a[2] =>
       /\ \A i \in a[1]..a[2] : seq[i] <= seq[a[2]]
       /\ \A i \in (a[2] + 1)..Len(seq) : seq[a[2]] <= seq[i]

Inv == DomainPartitions /\ Permutation(seq, orig) /\ RelativeSortedness

PCorrect ==
  pc = "term" =>
    /\ Permutation(seq, orig)
    /\ \A i \in 1..(Len(seq) - 1) : seq[i] <= seq[i + 1]

\* The abstract partition: any reorder of the interval that puts
\* elements at or below the pivot no greater than those above it.
Partitions ==
  { m \in Seq :
      /\ Len(m) = Len(seq)
      /\ \A i \in 1..Len(seq) : m[i] \in Values
      /\ \E a \in work : a[1] < a[2]
           /\ \E k \in a[1]..a[2] :
                /\ \A i \in a[1]..k : m[i] <= m[k]
                /\ \A i \in (k + 1)..a[2] : m[i] >= m[k]
                /\ \A i \in (a[2] + 1)..Len(seq) : seq[i] = m[i]
                /\ \A i \in 1..(a[1] - 1) : seq[i] = m[i] }

Init ==
  /\ seq \in Seq
  /\ orig = seq
  /\ work = {<<1, Len(seq)>>}
  /\ pc = "run"

\* The sort is the single thread of execution: one interval, one step.
Step ==
  /\ pc = "run"
  /\ work # {}
  /\ \E a \in work :
       /\ work' = work \ {a}
       /\ IF a[1] = a[2]
          THEN UNCHANGED <<seq, orig, work>>
          ELSE
            /\ \E k \in a[1]..a[2] :
                 /\ seq' \in Partitions
                 /\ work' = work \cup {<<a[1], k>>} \cup {<<k + 1, a[2]>>}
            /\ UNCHANGED orig
  /\ pc' = "run"

Terminate ==
  /\ pc = "run"
  /\ work = {}
  /\ pc' = "term"
  /\ UNCHANGED <<seq, orig, work>>

Stall ==
  /\ pc = "term"
  /\ UNCHANGED vars

Next == Step \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Step) /\ WF_vars(Terminate)

Termination ==
  pc = "term"

====