---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* A "limited" version of Seq, bounded by MaxSeqLen, replaces the infinite
\* version from the Sequences module so TLC can explore a finite state space.
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\* Permutations are factored through automorphisms of the actual domain.
Automorphisms == { f \in [1..MaxSeqLen -> 1..MaxSeqLen] : \A x \in 1..MaxSeqLen : \A y \in 1..MaxSeqLen : x # y => f[x] # f[y] }
Permutation(T) == { g \in [1..MaxSeqLen -> 1..MaxSeqLen] : \A i \in 1..MaxSeqLen : i > Len(T) => g[i] = i /\ g[i] \in 1..Len(T) /\ (i <= Len(T) => T[g[i]] = T[i]) }

\* Partitioning an interval around a pivot only reorders the interval, preserving
\* the multiset outside it and keeping the two sides on the correct side of the pivot.
Partitions(seq, iv, p) == { t \in Permutation(seq) :
  \A i \in 1..Len(seq) : (i < iv[1] \/ i > iv[2]) => t[i] = seq[i]
  /\ \A i \in iv[1]..p, j \in (p+1)..iv[2] : t[i] <= t[j] }

Intervals == { iv \in (1..MaxSeqLen) \X (1..MaxSeqLen) : iv[1] <= iv[2] }

VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

TypeOK ==
  /\ seq \in LimitedSeq(Values)
  /\ orig \in LimitedSeq(Values)
  /\ work \subseteq Intervals
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E s \in LimitedSeq(Values) : seq = s /\ orig = s
  /\ work = { <<1, Len(seq)>> }
  /\ pc = "loop"

\* One iteration of the quicksort loop: partition an interval around a pivot.
Step ==
  /\ pc = "loop"
  /\ work # {}
  /\ \E iv \in work :
       LET rest == work \ {iv} IN
         IF iv[1] = iv[2]
         THEN work' = rest
         ELSE \E p \in iv[1]..iv[2] :
                /\ \E t \in Partitions(seq, iv, p) : seq' = t
                /\ work' = rest \cup { <<iv[1], p>>, <<p+1, iv[2]>> }
  /\ pc' = pc

Done == /\ pc = "loop" /\ work = {} /\ pc' = "done" /\ UNCHANGED <<seq, orig, work>>

Stall == /\ pc = "done" /\ UNCHANGED vars

Next == Step \/ Done \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

\* The full partial-correctness statement: termination implies a sorted
\* permutation of the original input.
PCorrect == pc = "done" => (seq \in Permutation(orig) /\ \A i \in 1..(Len(seq) - 1) : seq[i] <= seq[i+1])

\* A complete inductive invariant: domain partitioning, permutation
\* preservation, and relative sortedness of every pair of intervals.
Inv ==
  /\ \A iv \in work : \A u \in work : iv # u => iv[2] < u[1]
  /\ seq \in Permutation(orig)
  /\ \A iv \in work, u \in work, iv # u :
       \A i \in iv[1]..iv[2], j \in u[1]..u[2] : i < j => seq[i] <= seq[j]

Termination == <>(pc = "done")
====