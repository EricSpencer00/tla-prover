---- MODULE Quicksort ----
EXTENDS Naturals, Sequences

CONSTANTS Values, MaxSeqLen

\* domain of the sequence at any moment (shrinks/expands as we model it)
Domain == 1..MaxSeqLen

Intervals == {i \in DOMAIN : \E a \in DOMAIN, b \in DOMAIN : i = <<a, b>>}

VARIABLES seq, orig, todo, pc

vars == <<seq, orig, todo, pc>>

\* permutation of the domain: a bijection that moves only elements inside i
PartialPermutation(i) ==
    {g \in [Domain -> Domain] :
        /\ \A x \in Domain \ (i[x] = x) => g[x] = x
        /\ g \in [i -> i]
        /\ \A x \in i : g[x] \in i
        /\ \A x, y \in i : g[x] = g[y] => x = y}

\* PARTITION is the abstracted partition step: it generates every sequence
\* that a concrete partitioning routine could produce for the chosen pivot
\* interval i (the pivot itself decides the split shape for the two subintervals)
Partition(i, pivot, s) ==
    {t \in [Domain -> Values] :
        /\ \A x \in DOMAIN \ i : t[x] = s[x]
        /\ \A x \in 1..(pivot - 1) : t[x] <= s[pivot]
        /\ \A x \in (pivot + 1)..MaxSeqLen : t[x] >= s[pivot]
        /\ \A x \in 1..MaxSeqLen, y \in 1..MaxSeqLen :
            (i[x] /\ i[y] /\ t[x] = t[y]) => x = y}

TypeOK ==
    /\ seq \in [Domain -> Values]
    /\ orig \in [Domain -> Values]
    /\ todo \subseteq Intervals
    /\ pc \in {"loop", "done"}

\* the partitioning decisions so far cover the whole domain without overlap:
\* everything below a chosen pivot is <= it, and everything above is >= it
SortedOnPartitions ==
    /\ \A i \in todo : \A x \in 1..(i[2] - 1), y \in 1..(i[2] - 1) :
        (i[1] <= x /\ x <= i[2] /\ i[1] <= y /\ y <= i[2]) => seq[x] <= seq[y]
    /\ \A i, j \in todo :
        (i # j) => ~(\A x \in DOMAIN : i[x] <=> j[x])

Init ==
    /\ \E s \in [Domain -> Values] : seq = s /\ orig = s
    /\ todo = {<<1, MaxSeqLen>>}
    /\ pc = "loop"

Loop ==
    /\ pc = "loop"
    /\ \E i \in todo :
        /\ i[1] = i[2]
        /\ todo' = todo \ {i}
        /\ UNCHANGED <<seq, orig>>
        \/ \E pivot \in Domain :
            /\ i[1] <= pivot /\ pivot <= i[2]
            /\ \E t \in Partition(i, pivot, seq) :
                seq' = t
            /\ todo' = (todo \ {i}) \cup {<<i[1], pivot - 1>>, <<pivot + 1, i[2>>}
    /\ UNCHANGED pc

Terminate ==
    /\ pc = "loop"
    /\ todo = {}
    /\ pc' = "done"
    /\ UNCHANGED <<seq, orig, todo>>

Stall ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == Loop \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Loop) /\ WF_vars(Terminate)

\* SAFETY: if the algorithm has terminated, its result is a sorted permutation
PCorrect ==
    /\ pc = "done" => (seq \in {orig \circ p : p \in PartialPermutation([1..MaxSeqLen] -> [1..MaxSeqLen])})
    /\ pc = "done" => SortedOnPartitions

\* PERMUTATION: the count of each value is unchanged by partitioning
ValueCountsUnchanged ==
    \A v \in Values :
        Cardinality({x \in DOMAIN : seq[x] = v}) = Cardinality({x \in DOMAIN : orig[x] = v})

\* TERMINAL: every interval has reached a singleton, so the sort is complete
AllSingletons ==
    todo = {}

\* INVARIANT: the loop invariant plus the sortedness it guarantees on the whole domain
Inv == ValueCountsUnchanged /\ AllSingletons /\ SortedOnPartitions

\* LIVENESS: the sort always eventually finishes
Termination == <> (pc = "done")

\* SEQUENCE: a FINITE version of Seq (bounded by MaxSeqLen) for model checking
LimitedSeq(S) == CHOOSE s \in Seq(Domain) : \A i \in DOMAIN : s[i] = S[i]
====