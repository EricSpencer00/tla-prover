---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* The partition operator is provided as a uninterpreted choice of sequences
\* that every real partition could produce. It takes the current sequence,
\* an interval to partition, and a pivot index, and yields a set of possible
\* resulting sequences that agree with the interval and pivot.
Partitions(s, lo, hi, p) ==
    { t \in [DOMAIN s -> Values] :
        /\ \A i \in DOMAIN s :
            (i < lo \/ i > hi) => t[i] = s[i]
        /\ \A i \in lo..p, j \in p+1..hi : t[i] <= t[j] }

Variables == <<seq, orig, tasks, pc>>
Interval == { i \in 1..MaxSeqLen : TRUE }

TypeOK ==
    /\ seq \in [DOMAIN -> Values]
    /\ orig \in [DOMAIN -> Values]
    /\ tasks \subseteq (Interval \X Interval)
    /\ pc \in {"loop", "done"}

Init ==
    /\ seq \in [DOMAIN -> Values]
    /\ seq # [i \in DOMAIN |-> CHOOSE v \in Values : TRUE]
    /\ orig = seq
    /\ tasks = {<<1, Len(seq)>>}
    /\ pc = "loop"

\* One iteration of the sorting loop, modelled as a single action that may
\* split an interval in place rather than first selecting it and then
\* partitioning it, to keep the model branching factor low.
Step ==
    \/ \E r \in tasks :
         /\ Cardinality(r) = 2
         /\ LET lo == r[1] IN LET hi == r[2] IN
              IF lo = hi THEN tasks' = tasks \ {r}
              ELSE \E p \in lo..hi :
                 \E t \in Partitions(seq, lo, hi, p) :
                     /\ seq' = t
                     /\ tasks' = (tasks \ {r})
                          \cup {<<lo, p>>, <<p+1, hi>>}
         /\ pc' = "loop"
    \/ (\A r \in tasks : Cardinality(r) = 2) /\ tasks = {}
         /\ pc' = "done"
    \/ pc = "done" /\ UNCHANGED <<seq, orig, tasks, pc>>

Next == Step

Spec == Init /\ [][Next]_Variables
        /\ WF_Variables(Step /\ pc = "loop")

\* Inductive invariant: intervals form a partition of the domain, the current
\* sequence is a permutation of the original, and no ordering relation is
\* ever violated between two intervals that are both present.
Inv ==
    /\ { <<r[1], r[2]>> : r \in tasks } = DOMAIN seq
    /\ \E f \in { f \in [DOMAIN -> DOMAIN] : \A i \in DOMAIN : f[i] # i } :
         (seq \o f) = orig
    /\ \A r1, r2 \in tasks :
         (r1[2] < r2[1]) => (\A i \in r1[2]..r2[1] : seq[i] <= seq[i+1])

PCorrect == \A i \in DOMAIN seq : seq[i] \in Values
Termination == <>(pc = "done")

====