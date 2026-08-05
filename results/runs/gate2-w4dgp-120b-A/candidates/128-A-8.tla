---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* A bounded version of the generic Seq operator, since the standard one
\* from Sequences is infinite and makes exhaustive model checking impossible.
LimitedSeq(T, n) == {s \in Seq(T) : Len(s) <= n}

VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

Intervals == UNION {SUBSET (1..n \X 1..n) : n \in Nat}
Parts == INTERVAL(1)
Domain == UNION {1..n : n \in Nat}
Auto(f) == {g \in [f :> f] : \A x \in f : g[g[x]] = x}

TypeOK ==
  /\ seq \in LimitedSeq(Values, MaxSeqLen)
  /\ orig = seq
  /\ work \subseteq Intervals
  /\ pc \in {"main", "halt"}

Sorted(s) == \A i \in 1..Len(s) - 1 : s[i] <= s[i+1]

Partitions(s) ==
  {t \in Intervals \X (Domain \X Domain) : t[1] \in Intervals /\ t[2] \subseteq Auto(Domain)}

\* The Partition action models the partition step abstractly; it chooses
\* any outcome that some concrete partition routine could produce.
Partition(s, p, i) ==
  \E t \in Partitions(s) : <<p, i>> \in t[1] /\ t[2] \in Domain \X Domain /\ s' = t[2]

IntervalsSubset(i, j) ==
  \/ i[2] + 1 = j[1]
  \/ i[1] = j[2] + 1
  \/ i[2] < j[1]
  \/ j[2] < i[1]

\* Two sorted intervals in a common sequence must be correctly ordered
\* relative to each other if they do not overlap.
RelativeOrder(s) ==
  \A i, j \in work :
    Sorted(s) \/ s[i[2]] <= s[j[1]] \/ s[j[2]] <= s[i[1]] \/ IntervalsSubset(i, j)

Inv ==
  /\ work \subseteq Intervals
  /\ Seq(Domain) \o (Auto(Domain) \cup {orig}) = seq \/ orig = seq
  /\ RelativeOrder(seq)

Init ==
  /\ seq \in LimitedSeq(Values, MaxSeqLen) /\ seq # <<>>
  /\ orig = seq
  /\ work = {<<1, Len(seq)>>}
  /\ pc = "main"

Main ==
  /\ pc = "main"
  /\ \E i \in work :
       /\ IF i[1] = i[2]
          THEN work' = work \ {i}
          ELSE \E c, d \in Domain :
                 /\ c < d /\ c \in i /\ d \in i
                 /\ \E t \in Partitions(seq) :
                      /\ t[1] = i
                      /\ t[2] = <<c, d>>
                      /\ seq' = t[2]
                 /\ work' = (work \ {i}) \cup {<<i[1], c>>, <<d, i[2]>>}
  /\ UNCHANGED <<orig, pc>>

Finish ==
  /\ pc = "main" /\ work = {} /\ pc' = "halt"
  /\ UNCHANGED <<seq, orig, work>>

Stall ==
  /\ pc = "halt"
  /\ UNCHANGED vars

Next == Main \/ Finish \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Main)

PCorrect == (pc = "halt") => (Seq(Domain) \o {orig} \/ (seq = orig /\ Sorted(seq)))

Termination == <>(pc = "halt")

====