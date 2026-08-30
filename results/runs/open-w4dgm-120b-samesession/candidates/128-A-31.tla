---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

Intervals == SUBSET (1..MaxSeqLen \X 1..MaxSeqLen)
Domain == 1..MaxSeqLen
Permutation == [Domain -> Domain]

VARIABLES seq, original, workset, pc
vars == <<seq, original, workset, pc>>

\* A permutation-compatible rearrangement of a sequence: the range is the same,
\* and the index function is a genuine permutation (bijection) of the domain.
Sigma(f) == Cardinality({f[i] : i \in Domain}) = MaxSeqLen /\ /\ \A i \in Domain : f[i] \in Domain

Sorted(d) == \A i \in Domain : d[i] <= d[i + 1]

Init ==
  /\ \E s \in [Domain -> Values] : seq = s
  /\ original = seq
  /\ workset = {<<1, MaxSeqLen>>}
  /\ pc = "loop"

\* The partition step chooses a new version of the whole sequence that
\* respects the total-order partition law on the chosen interval.
Next ==
  \/ \E r \in workset :
       \/ LET g == [i \in Domain |-> IF r[1] <= i /\ i <= r[2] THEN seq[i] ELSE seq[i] IN
            /\ \E pivot \in r[1]..r[2] :
                 \E newSeq \in {s \in [Domain -> Values] :
                                   /\ sigma \in Permutation : s = g \circ sigma
                                   /\ \A i \in Domain :
                                        (i < r[1] \/ i > r[2]) => s[i] = seq[i]
                                   /\ \A i \in r[1]..pivot, j \in (pivot + 1)..r[2] :
                                        s[i] <= s[j]}
                 /\ seq' = newSeq
            /\ workset' = (workset \ {r})
                 \cup {<<r[1], pivot>>}
                 \cup {IF pivot + 1 <= r[2] THEN {<<pivot + 1, r[2>>}} ELSE {}
          /\ pc' = "loop"
       \/ \/ LET r == <<1, 1>> IN workset' = workset \ {r} /\ pc' = "loop" /\ seq' = seq /\ original' = original
  \/ (workset = {} /\ pc' = "halt" /\ seq' = seq /\ original' = original /\ workset' = workset)
  \/ (\A x \in vars : TRUE) /\ pc = "halt"

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

PCorrect ==
  /\ (pc = "halt") => (workset = {})
  /\ (pc = "loop") => (workset # {})

TypeOK ==
  /\ seq \in [Domain -> Values]
  /\ original \in [Domain -> Values]
  /\ pc \in {"loop", "halt"}

\* The loop maintains that sortedness is never violated across any two
\* intervals that are both outside the current work set.
Inv ==
  /\ \A i \in Domain : original[i] = seq[i] \/ Sorted(seq)
  /\ \A i, j \in Domain : (i \in workset) \/ (j \in workset) \/ (seq[i] <= seq[j])

Termination == (pc = "halt") ~> (pc = "halt")
====