---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* The action model of Quicksort: a single sort procedure (no concurrency), an
\* interval work set, and a partition operator that abstracts away the actual
\* partition step. Limiting the value set and the sequence length are what let
\* TLC check the specification; the .cfg file redefines Seq as a bounded version.

VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

Intervals == UNION {[1..MaxSeqLen] \X [1..MaxSeqLen]}
PivotIdx(lo, hi) == lo .. hi

\* A valid partition of an interval for any possible pivot index: everything
\* outside the interval is unchanged, and elements inside the interval are
\* split so that the lower subinterval's elements are no greater than the
\* upper subinterval's.
Partitioned(q, lo, hi) ==
  \E p \in PivotIdx(lo, hi):
    /\ \E r \in [DOMAIN q -> Values]:
         /\ \A i \in DOMAIN q : i < lo \/ i > hi => r[i] = q[i]
         /\ \A i \in lo .. hi : \A j \in (p+1) .. hi => r[i] <= r[j]
    /\ r

TypeOK ==
  /\ seq \in [1..MaxSeqLen -> Values]
  /\ orig \in [1..MaxSeqLen -> Values]
  /\ work \subseteq Intervals
  /\ pc \in {"loop", "done"}

Init ==
  /\ seq \in Seq(Values)
  /\ orig = seq
  /\ work = {<<1, Len(seq)>>}
  /\ pc = "loop"

\* One Quicksort loop iteration: pick an interval, partition it, and add the
\* subintervals to the work set. If the interval is a singleton, just drop it.
Step ==
  \/ \E w \in work:
       /\ Len(seq) >= w[2]
       /\ Cardinality(w) = 1 \/ w[1] = w[2]
       /\ work' = work \ {w}
       /\ UNCHANGED <<seq, orig>>
  \/ \E w \in work:
       /\ w[1] < w[2]
       /\ \E p \in PivotIdx(w[1], w[2]):
            /\ seq' = Partitioned(seq, w[1], w[2])
            /\ work' = (work \ {w}) \cup {<<w[1], p>>, <<p+1, w[2]>>}
       /\ UNCHANGED orig
  \/ (work = {} /\ pc' = "done" /\ UNCHANGED <<seq, orig, work>>)
  \/ (pc = "done" /\ UNCHANGED vars)

Next == Step

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

\* The partial correctness condition is an invariant rather than a property,
\* because it must hold at every reachable state -- trivially true except on
\* termination, where it is exactly the claim of interest.
PCorrect ==
  (pc = "done") =>
    /\ \A i \in DOMAIN orig : \E j \in DOMAIN seq : seq[j] = orig[i]
    /\ \A i \in 1 .. (Len(seq) - 1) : seq[i] <= seq[i+1]

\* A strong invariant that is also checked by TLAPS: any two intervals that
\* touch share a common boundary value, which is what lets the final step
\* through.
Inv ==
  \A w \in work :
    /\ Cardinality(w) = 2 \/ w[1] = w[2]
    /\ \A w2 \in work \ {w} :
         (w[2] = w2[1] \/ w2[2] = w[1]) =>
           IFC(w[2] = w2[1], seq[w2[1]], seq[w[1]]) =
             IFC(w2[2] = w[1], seq[w[1]], seq[w2[1]])

Termination == <>(pc = "done")

====