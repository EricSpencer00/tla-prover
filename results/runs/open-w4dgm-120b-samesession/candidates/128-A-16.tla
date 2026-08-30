---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* domain: indices of the sequence up to its current length
Domain == 1..MaxSeqLen

\* Compute the restricted domain of the actual current prefix of seq
DomainOf(s) == 1..Len(s)

\* A permutation: an automorphism of the domain of the current prefix
Permutation == [Domain -> Domain]
DomainAutomorphisms == {p \in Permutation : \A a, b \in Domain : (p[a] = p[b]) => (a = b)}
Compose(f, g) == [x \in Domain |-> f[g[x]]]

\* Partitioning is a nondeterministic choice of a valid rearrangement of one interval:
\* all values outside the interval stay put; every value at or below the pivot is
\* no greater than any value above it.
Partition(a, b, p, s) ==
    {t \in [Domain -> Values] :
        /\ \A i \in Domain \ DomainOf(s) : t[i] = s[i]
        /\ \A i \in a..b : p[i] \in Values
        /\ \A i \in a..b : \A j \in a..b : (i <= p AND j > p) => (t[i] <= t[j])}

VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

TypeOK ==
    /\ seq \in [Domain -> Values]
    /\ orig \in [Domain -> Values]
    /\ work \subseteq (Domain \X Domain)
    /\ pc \in {"working", "done"}

Init ==
    /\ \E s \in [Domain -> Values] :
        /\ seq = s
        /\ orig = s
    /\ work = {<<1, MaxSeqLen>>}
    /\ pc = "working"

\* One loop iteration: pick an interval, partition it around a pivot, and split it
Step ==
    /\ pc = "working"
    /\ \E a, b \in Domain :
        /\ <<a, b>> \in work
        /\ IF a = b THEN work' = work \ {<<a, b>>}
           ELSE \E p \in a..b, t \in Partition(a, b, p, seq) :
                /\ seq' = t
                /\ work' = (work \ {<<a, b>>}) \cup {<<a, p>>, <<p + 1, b>>}
    /\ pc' = IF work = {<<a, b>>} THEN "done" ELSE pc

Stall ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == Step \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

PCorrect ==
    /\ \A a, b \in Domain : (a <= b) => (<<a, b>> \in work <=> a <= b /\ b <= Len(seq))
    /\ \A i, j \in Domain :
        ((i <= Len(seq) /\ j <= Len(seq) /\ i > j) => (seq[i] >= seq[j]))
    /\ \A i \in Domain : i > Len(seq) => (seq[i] = orig[i])

\* Each interval is a domain block, the sequence stays a domain permutation, and
\* intervals' values respect the concatenation order -- together these imply sortedness.
Inv ==
    /\ PCorrect
    /\ Len(seq) = MaxSeqLen
    /\ \A i, j \in Domain : (i <= Len(seq) /\ j <= Len(seq) /\ i > j) => (seq[i] >= seq[j])

TypeOK2 == TypeOK

Termination == <>(pc = "done")

====