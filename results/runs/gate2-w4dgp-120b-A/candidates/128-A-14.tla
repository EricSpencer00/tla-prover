---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, Permutations

CONSTANTS Values, MaxSeqLen

VARIABLES seq, original, workset, pc
vars == <<seq, original, workset, pc>>

\* A sorted interval has no descending inversion inside it.
Sorted(i, j) == \A k \in i..j-1 : seq[k] <= seq[k+1]

\* The partition operator is nondeterministic: it collects *all* possible
\* results of a valid partition step over a chosen interval and pivot,
\* and the step driver below picks one of them.
Partitioned(i, j, p) == {f \in Permutations(Domain(seq)) :
    (\A k \in 1..Len(seq) : k < i \/ k > j => f[k] = seq[k])
    /\ (\A k \in i..j : k <= p => f[k] <= f[p])
    /\ (\A k \in i..j : k > p => f[k] >= f[p])
}

TypeOK ==
    /\ seq \in LimitedSeq(MaxSeqLen, Values)
    /\ original \in LimitedSeq(MaxSeqLen, Values)
    /\ workset \subseteq SUBSET (Domain(seq) \X Domain(seq))
    /\ pc \in {"loop", "done"}

Init ==
    /\ \E s \in LimitedSeq(MaxSeqLen, Values) : Len(s) > 0 /\ seq = s
    /\ original = seq
    /\ workset = {<<1, Len(seq)>>}
    /\ pc = "loop"

Main ==
    /\ pc = "loop"
    /\ \/ \E interval \in workset :
          LET i == interval[1] IN
          LET j == interval[2] IN
          IF i = j THEN
              /\ workset' = workset \ {interval}
              /\ UNCHANGED seq
          ELSE
              \/ \E p \in i..j :
                  /\ Partitioned(i, j, p) # {}
                  /\ \E f \in Partitioned(i, j, p) : seq' = f
                  /\ workset' = (workset \ {interval}) \cup {<<i, p>>, <<p+1, j>>}
    /\ pc' = "loop"
    \/ (workset = {} /\ pc' = "done" /\ UNCHANGED <<seq, original, workset>>)

Done ==
    /\ pc = "done"
    /\ UNCHANGED <<seq, original, workset, pc>>

Next == Main \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Main)

\* The algorithm is correct: the final sequence is a permutation of the
\* input and is fully sorted.
PCorrect ==
    pc = "done" =>
        /\ (seq = Permutations(Domain(seq)) @@ original)
        /\ \A i \in Domain(seq) : Sorted(i, Len(seq))

\* Inductive invariant: every interval in the work set already has its
\* interior sorted, and the sequence as a whole is a permutation of the
\* original input; sorting is only completed once the set drains.
Inv ==
    /\ seq = Permutations(Domain(seq)) @@ original
    /\ \A interval \in workset : Sorted(interval[1], interval[2])

Termination == <>(pc = "done")

====