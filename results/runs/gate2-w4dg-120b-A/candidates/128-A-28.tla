---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen, Seq

ASSUME Values \subseteq Nat /\ Cardinality(Values) > 0

Indices == 1..Len(Seq)

VARIABLES seq, original, todo, pc
vars == <<seq, original, todo, pc>>

Intervals == (Indices \X Indices) \cup {<<0, 0>>}

\* A refined interval is one that lies fully inside the current sequence's
\* domain and where the lower bound is no greater than the upper.
IsRefined(i) == i[1] \in Indices /\ i[2] \in Indices /\ i[1] <= i[2]

\* A valid partition leaves everything outside the interval untouched and
\* guarantees every element at or below the pivot is no greater than any
\* element above it.
Partitions == {s \in Sequences(Values) :
                  Cardinality(s) = Len(Seq) /\
                  \E p \in Indices :
                    \A i \in Indices, j \in Indices :
                      (i <= p /\ p < j) => s[i] <= s[j]}

NxtSeq(s, i, p) == {t \in Partitions :
                       \A k \in Indices :
                         (k < i[1] \/ k > i[2]) => t[k] = s[k]}

\* Elements below the pivot are no greater than elements above it; this
\* relation is all that the abstract partition step needs.
SortedBelow(i, s) == \A k \in Indices, l \in Indices :
                       (i[1] <= k /\ k <= i[2] /\ k <= l /\ l <= i[2] /\ k <= l) =>
                         s[k] <= s[l]

IsSorted == \A i, j \in Indices : i <= j => seq[i] <= seq[j]

TypeOK ==
  /\ seq \in Sequences(Values)
  /\ original \in Sequences(Values)
  /\ todo \subseteq Intervals
  /\ pc \in {"main", "done"}

Init ==
  /\ /\ Len(Seq) > 0
     /\ seq = Seq
     /\ original = Seq
  /\ /\ Len(Seq) <= MaxSeqLen
     /\ todo = {<<1, Len(Seq)>>}
  /\ pc = "main"

\* An interval of length one is a leaf and is simply removed from the work set.
Step ==
  /\ pc = "main"
  /\ \E i \in todo :
       /\ /\ IsRefined(i)
          /\ todo' = todo \ {i}
       /\ IF i[1] = i[2]
          THEN /\ seq' = seq
               /\ UNCHANGED <<original, todo>>
          ELSE
            /\ \E p \in Indices :
                 /\ p \in i[1]..i[2]
                 /\ SortedBelow(i, seq)
                 /\ seq' \in NxtSeq(seq, i, p)
            /\ LET lo == <<i[1], p>> IN
               /\ LET hi == <<p + 1, i[2]>> IN
                 /\ todo' = todo \cup {lo, hi}
          /\ UNCHANGED original
  /\ UNCHANGED pc

Terminate ==
  /\ pc = "main"
  /\ todo = {}
  /\ pc' = "done"
  /\ UNCHANGED <<seq, original, todo>>

Idle ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == Step \/ Terminate \/ Idle

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

\* The final result must be a permutation of the input and be sorted.
PCorrect ==
  /\ (pc = "done") => (seq \in Permutations(original) /\ IsSorted)

\* A refined partition set always covers the whole domain, each partition
\* appears at most once, and neighboring partitions are relatively sorted.
Inv ==
  /\ Union({i[1]..i[2] : i \in todo \cup {<<1, Len(seq)>>}}) = Indices
  /\ \A i, j \in todo \cup {<<1, Len(seq)>>} : (i # j /\ IsRefined(i) /\ IsRefined(j)) => (i[2] < j[1] \/ j[2] < i[1])
  /\ \A i \in todo \cup {<<1, Len(seq)>>} : IsRefined(i) => SortedBelow(i, seq)

Termination == (pc = "done")

====