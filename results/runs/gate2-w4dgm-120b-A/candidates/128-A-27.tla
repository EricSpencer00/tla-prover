---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

VARIABLES seq, orig, work, pc
vars == <<seq, orig, work, pc>>

Intervals == {I \in (1..MaxSeqLen) \X (1..MaxSeqLen) : I[1] <= I[2]}
\* Two intervals are adjacent if the first is exactly before the second.
Adjacent(I, J) == (I[1] = J[1] /\ I[2] = J[2]) \/ (I[2] + 1 = J[1] \/ J[2] + 1 = I[1])

TypeOK ==
    /\ seq \in Seq(Values)
    /\ Len(seq) <= MaxSeqLen
    /\ orig \in Seq(Values)
    /\ Len(orig) <= MaxSeqLen
    /\ work \subseteq Intervals
    /\ pc \in {"loop", "done"}

Init ==
    \E s \in Seq(Values) :
        /\ s # <<>>
        /\ seq = s
        /\ orig = s
        /\ work = {<<1, Len(s)>>}
        /\ pc = "loop"

\* The partition operator is nondeterministic: it produces any permutation
\* that leaves elements outside the interval unchanged and does not straddle
\* the pivot index.
PartitionOperator ==
    {t \in Seq(Values) :
        /\ Len(t) = Len(seq)
        /\ \A k \in 1..Len(seq) : k < I[1] \/ k > I[2] => t[k] = seq[k]
        /\ \A a, b \in I[1]..I[2] :
            (a <= I[3] /\ b > I[3]) => t[a] <= t[b]}
\* The partition interval is [lo..hi] with pivot at p; it must be a subrange.
WorkStep ==
    \E I \in work :
        /\ I[2] - I[1] >= 1
        /\ \E p \in I[1]..I[2] :
            /\ \E s \in PartitionOperator :
                /\ seq' = s
                /\ work' = (work \ {I})
                    \cup {<<I[1], p>>, <<p + 1, I[2]>>}
        /\ pc' = pc
    \/ \E I \in work :
        /\ I[2] = I[1]
        /\ work' = work \ {I}
        /\ pc' = pc
        /\ seq' = seq
        /\ orig' = orig

Next == WorkStep \/ (pc = "done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

PCorrect ==
    /\ \A I, J \in work : Adjacent(I, J) => I = J
    /\ (work = {} => pc = "done")

SortedRange(f, a, b) ==
    \A i \in a..b-1 : f[i] <= f[i+1]
Permuted(g, f) ==
    \E h \in [1..Len(g) -> 1..Len(g)] :
        /\ \A x, y \in 1..Len(g) : h[x] = h[y] => x = y
        /\ \A i \in 1..Len(g) : g[i] = f[h[i]]

Inv ==
    /\ PCorrect
    /\ Permuted(seq, orig)
    /\ \A i \in 1..MaxSeqLen : (i <= Len(seq) /\ i >= 2) => seq[i - 1] <= seq[i]

Termination == pc = "done"
====