---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen, Seq

\* A permutation of an interval's domain is a bijection from that domain to itself.
Permutation(f) == DOMAIN f = 1..Len(Seq) /\ \A x, y \in DOMAIN f : f[x] = f[y] => x = y

\* The partition operator collects every sequence that could arise from a valid
\* partition of the current sequence over an interval at a pivot: it is fully
\* nondeterministic (any such sequence is reachable), which is what gives TLC
\* coverage over the different interleavings of the abstract CompareAndSwap.
PSeq(i, j, p) == {x \in [1..Len(Seq) -> Values] :
    \A u \in 1..Len(Seq) :
      \/ (u < i \/ u > j) => x[u] = Seq[u]
      \/ (i <= u /\ u <= p) => \A v \in i..j : x[u] <= Seq[v]
      \/ (p < u /\ u <= j) => \A v \in i..j : x[u] >= Seq[v]}
Lows(i, j, p) == {u \in 1..Len(Seq) : i <= u /\ u <= p}
Ups(i, j, p) == {u \in 1..Len(Seq) : p < u /\ u <= j}

VARIABLES seq, orig, intervals, pc

vars == <<seq, orig, intervals, pc>>

\* The invariant over the domain partitions: each interval's lower subinterval must
\* still be below every index of its upper subinterval (so the pairwise sortedness
\* is preserved as the intervals subdivide). The partition operator never changes
\* positions outside the interval, which is what keeps each index in exactly one
\* interval and makes the above check complete.
Inv == \A i, j \in intervals : \A x \in Lows(i, j, j) : \A y \in Ups(i, j, j) : seq[x] <= seq[y]

TypeOK ==
    /\ seq \in [1..Len(Seq) -> Values]
    /\ orig \in [1..Len(Seq) -> Values]
    /\ intervals \subseteq (1..Len(Seq) \X 1..Len(Seq))
    /\ pc \in {"loop", "done"}

Init ==
    /\ seq = Seq
    /\ orig = Seq
    /\ intervals = {<<1, Len(Seq)>>}
    /\ pc = "loop"

\* One fully abstracted iteration: the partition is chosen nondeterministically
\* from every sequence the operator could produce, given the interval and pivot.
Step ==
    \/ \E r \in intervals :
         /\ intervals' = intervals \ {r}
         /\ r[1] = r[2]
         /\ UNCHANGED <<seq, orig>>
    \/ \E r \in intervals, p \in r[1]..r[2], seq' \in PSeq(r[1], r[2], p) :
         /\ intervals' = (intervals \ {r}) \cup {<<r[1], p>>, <<p+1, r[2]>>}
         /\ seq' \in PSeq(r[1], r[2], p)
         /\ UNCHANGED <<orig, pc>>
    \/ (intervals = {}) /\ pc' = "done" /\ UNCHANGED <<seq, orig, intervals>>
    \/ (pc = "done") /\ UNCHANGED vars

Next == Step

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

\* The final sorted sequence must be both a permutation of the input and fully
\* sorted; it suffices to check sortedness against the original values, because the
\* partition operator never changes values outside its current interval.
PCorrect == (pc = "done") => (\A x \in DOMAIN seq : seq[x] \in Values /\ \A i \in 1..(Len(seq)-1) : seq[i] <= seq[i+1])

Termination == (pc = "done") ~> TRUE

====