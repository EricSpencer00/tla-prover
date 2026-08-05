---- MODULE Quicksort ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* The sort is modeled as a single actor, the sort procedure itself.
\* Sequence is redefined below (via the .cfg) to be a length-limited
\* version of the full Sequences.Seq operator.
VARIABLES sequence, originalSeq, workSet, pc

vars == <<sequence, originalSeq, workSet, pc>>

Intervals == UNION { [1 .. n -> [1 .. n]] : n \in 1..MaxSeqLen }

Domain(sq) == { i \in 1..Len(sq) : TRUE }
Automorphisms(n) == { f \in [1..n -> 1..n] : f \in [1..n -> 1..n] /\ \A x, y \in 1..n : f[x] = f[y] => x = y }
Permutation(s) == { s \circ f : f \in Automorphisms(Len(s)) }
Sorted(s) == \A i \in 1..(Len(s) - 1) : s[i] <= s[i+1]
Ordered(s, l, u) == \A i \in l..u, j \in u+1..Len(s) : s[i] <= s[j]

\* A partition step chooses any sequence that could result from a genuine
\* partition procedure: it must be a permutation of the input, leave
\* elements outside the interval alone, and order the two halves.
Partition(s, l, u, p) == { t \in Permutation(s) :
    \A i \in 1..Len(s) : (i < l \/ i > u) => t[i] = s[i]
    /\ \A i \in l..p, j \in p+1..u : t[i] <= t[j] }

TypeOK ==
    /\ sequence \in Sequence(Values)
    /\ Len(sequence) <= MaxSeqLen
    /\ originalSeq \in Sequence(Values)
    /\ workSet \in SUBSET Intervals
    /\ pc \in {"main", "done"}

Init ==
    /\ \E s \in { x \in Sequence(Values) : x # <<>> /\ Len(x) <= MaxSeqLen } : sequence = s /\ originalSeq = s
    /\ workSet = {[1 .. Len(sequence) -> [1 .. Len(sequence)] ]}
    /\ pc = "main"

MainLoop ==
    /\ pc = "main"
    /\ \E iv \in workSet :
        LET l == iv[1] IN LET u == iv[2] IN LET n == Len(sequence) IN
        /\ workSet' = workSet \ {iv}
        /\ IF l = u THEN workSet' ELSE
             /\ \E p \in l..u :
                  /\ \E t \in Partition(sequence, l, u, p) : sequence' = t
                  /\ workSet' = workSet' \cup {[l .. p -> [1 .. n]]} \cup {[p+1 .. u -> [1 .. n]]}
    /\ UNCHANGED <<originalSeq, pc>>

Terminate ==
    /\ pc = "main"
    /\ workSet = {}
    /\ pc' = "done"
    /\ UNCHANGED <<sequence, originalSeq, workSet>>

Stall == /\ pc = "done" /\ UNCHANGED vars

Next == MainLoop \/ Terminate \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(MainLoop)

\* Termination: the algorithm reaches its final state.
Termination == <>(pc = "done")

\* Partial correctness: on termination the result is a permutation of the
\* original and is fully sorted.
PCorrect ==
    (pc = "done") => (sequence \in Permutation(originalSeq) /\ Sorted(sequence))

Inv ==
    /\ \E d \in Domain(sequence) : \A iv \in workSet : d \subseteq iv
    /\ sequence \in Permutation(originalSeq)
    /\ \A iv \in workSet : Ordered(sequence, iv[1], iv[2])

\* The .cfg replaces Sequence with a bounded version.  Here we keep the name
\* Sequence in scope for internal definitions but rebind it at runtime.
Sequence == LimitedSeq

====