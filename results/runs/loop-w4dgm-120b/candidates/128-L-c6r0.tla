---- MODULE Quicksort ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* Quicksort on a bounded, nondeterministically chosen input sequence.  The
\* partition operator below abstracts the actual swapping/joining steps and
\* simply chooses any sequence consistent with a valid partition result.

Indices == 1..MaxSeqLen

VARIABLES seq, origSeq, work, pc

vars == <<seq, origSeq, work, pc>>

Intervals == [first : 1..MaxSeqLen, last : 1..MaxSeqLen]

\* A "partition" is any permutation of the domain preserving the divide at the
\* pivot: everything at or below the pivot is no greater than everything above.
Partitions(i, j, k) ==
  { f \in [Indices -> Values] :
      /\ \A a \in 1..MaxSeqLen : (a < i \/ a > j) => f[a] = seq[a]
      /\ \A a \in i..k, b \in (k + 1)..j : f[a] <= f[b] }

TypeOK ==
  /\ seq \in [Indices -> Values]
  /\ origSeq \in [Indices -> Values]
  /\ work \subseteq Intervals
  /\ pc \in {"main", "done"}

Init ==
  /\ \E s \in Seq(Values) :
       /\ Len(s) >= 1
       /\ seq = s
       /\ origSeq = s
  /\ work = {[first |-> 1, last |-> Len(seq)]}
  /\ pc = "main"

IsSingleton(w) == w.first = w.last

Terminate ==
  /\ pc = "main"
  /\ work = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, origSeq, work>>

\* The single destructive step: choose any valid partition result for the
\* interval, then subdivide it into two new intervals.
ProcessInterval(w) ==
  /\ pc = "main"
  /\ w \in work
  /\ work' = work \ {w}
  /\ IF IsSingleton(w) THEN seq' = seq
     ELSE
       /\ \E k \in w.first..(w.last - 1) :
            /\ \E ns \in Partitions(w.first, w.last, k) : seq' = ns
            /\ work' = work' \cup {[first |-> w.first, last |-> k],
                                   [first |-> k + 1, last |-> w.last]}
  /\ UNCHANGED <<origSeq, pc>>

Next ==
  \/ Terminate
  \/ \E w \in work : ProcessInterval(w)
  \/ (pc = "done" /\ UNCHANGED vars)

\* SAFETY PROPERTY (partial correctness): on termination the result is a
\* sorted permutation of the original sequence.
PCorrect ==
  (pc = "done") =>
    /\ seq \in (DomainPermutations(1..Len(seq)) @@ origSeq)
    /\ \A a \in 1..(Len(seq) - 1) : seq[a] <= seq[a + 1]

\* STRONGer, inductive invariant: every active interval is internally sorted
\* and well-separated from every other active interval.
Inv ==
  /\ \A w \in work : \A a, b \in w.first..w.last : seq[a] <= seq[b]
  /\ \A w1 \in work, w2 \in work :
       (w1 # w2) =>
         \/ w1.last < w2.first
         \/ w2.last < w1.first
         \/ \A a \in w1.first..w1.last, b \in w2.first..w2.last : seq[a] <= seq[b]

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* PROGRESS PROPERTY: the algorithm always eventually terminates.
Termination == <>(pc = "done")

\* The domain-permutation operator is by construction an automorphism of the
\* index domain and is needed to state PCorrect.
DomainPermutations ==
  { g \in [Indices -> Indices] : \A x, y \in Indices : (x # y) => g[x] # g[y] }

\* Finite variant of Seq for model checking bounded runs.
LimitedSeq(f, n) == IF n = 0 THEN << >> ELSE << f[n] >> \o LimitedSeq(f, n - 1)
====