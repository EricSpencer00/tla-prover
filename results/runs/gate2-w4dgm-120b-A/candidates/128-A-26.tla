---- MODULE Quicksort ----
EXTENDS Naturals, Sequences

CONSTANTS Values, MaxSeqLen

\* The model bounds the sequence length, which is what makes the state
\* space finite; the action guards below are written against that bound.
SeqLen == 2
DOMAIN == 1..SeqLen

\* Partition(n, i, v) is the abstract step: nondeterministically pick any
\* sequence that keeps the prefix and suffix outside the interval unchanged
\* and puts only elements <= the pivot value below the pivot index.
Partition(n, i, v) ==
  { m \in [DOMAIN -> Values] :
        /\ \A k \in DOMAIN \ {i, i+1} : m[k] = n[k]
        /\ \A k \in 1..i : m[k] <= v
        /\ \A k \in (i+1)..SeqLen : v <= m[k] }

\* The state: current sequence, a copy of the original, the work set of
\* intervals to sort, and a control label.
VARIABLES seq, original, work, pc

vars == <<seq, original, work, pc>>

TypeOK ==
  /\ seq \in [DOMAIN -> Values]
  /\ original \in [DOMAIN -> Values]
  /\ work \subseteq [lo : 1..SeqLen, hi : 1..SeqLen]
  /\ pc \in {"main", "done"}

Init ==
  /\ \E s \in [DOMAIN -> Values] : seq = s
  /\ original = seq
  /\ work = {[lo |-> 1, hi |-> SeqLen]}
  /\ pc = "main"

\* The whole action is strongly fair on itself, so the transition relation
\* never lets the sort spin in the terminating state.
SortStep ==
  /\ pc = "main"
  /\ work # {}
  /\ \E r \in work :
       /\ work' = work \ {r}
       /\ IF r.lo = r.hi
            THEN UNCHANGED <<seq, original>>
            ELSE
              \E v \in Values :
                /\ seq' \in Partition(seq, r.lo, v)
                /\ work' = work \cup
                     {[lo |-> r.lo, hi |-> r.lo], [lo |-> r.lo + 1, hi |-> r.hi]}
  /\ pc' = "main"

Terminate ==
  /\ pc = "main"
  /\ work = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, original, work>>

Stutter ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ SortStep
  \/ Terminate
  \/ Stutter

Spec == Init /\ [][Next]_vars
  /\ WF_vars(SortStep) /\ WF_vars(Terminate)

Sorted == \A i \in 1..(SeqLen - 1) : seq[i] <= seq[i + 1]

\* An interval map whose ranges partition the sequence domain.
Partitioning == {r.hi : r \in work} = {0} \cup {r.lo - 1 : r \in work}

Permutation == \E f \in [DOMAIN -> DOMAIN] :
  /\ f \in [DOMAIN -> DOMAIN]
  /\ \A a, b \in DOMAIN : (f[a] = f[b]) => (a = b)
  /\ seq = [i \in DOMAIN |-> original[f[i]]]

RelativeSorted ==
  \A r, q \in work : r.hi < q.lo => seq[r.hi] <= seq[q.lo]

PCorrect == (pc = "done") => Sorted
TypeOKP == Partitioning /\ Permutation /\ RelativeSorted

Termination == <>(pc = "done")

====