---- MODULE Quicksort ----
EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen

\* An interval is a contiguous range of indices into the sequence.
Interval == [low: 1..MaxSeqLen, hi: 1..MaxSeqLen]

\* The "finite" version of the Seq operator from Sequences, kept bounded.
LimitedSeq(S) == CHOOSE f \in [1..Len(S) -> Values] :
                    \A i \in 1..Len(S) : f[i] = S[i]

\* A sub-sequence of seq confined to the given index interval.
SubSeq(seq, int) == [i \in int.low .. int.hi |-> seq[i]]

\* A permutation of a sequence: a reordering of its domain indices.
Permutation(seq) ==
  \E g \in [1..Len(seq) -> 1..Len(seq)] :
    /\ \A a, b \in 1..Len(seq) : g[a] = g[b] => a = b
    /\ [i \in 1..Len(seq) |-> seq[g[i]]]

VARIABLES seq, orig, todo, pc

vars == <<seq, orig, todo, pc>>

TypeOK ==
  /\ seq \in Seq(Values)
  /\ orig \in Seq(Values)
  /\ todo \subseteq Interval
  /\ Len(seq) <= MaxSeqLen
  /\ pc \in {"loop", "done"}

Init ==
  /\ \E s \in Seq(Values) :
        /\ s # <<>>
        /\ seq = s
        /\ orig = s
  /\ todo = {[low |-> 1, hi |-> Len(seq)]}
  /\ pc = "loop"

\* One iteration of the Quicksort loop: an interval is partitioned around
\* a pivot and replaced by its two subintervals.
Step ==
  /\ pc = "loop"
  /\ \E int \in todo :
       /\ int \in todo
       /\ LET rest == todo \ {int} IN
          IF int.low = int.hi
          THEN /\ todo' = rest
               /\ UNCHANGED <<seq>>
          ELSE
            /\ \E k \in int.low..int.hi :
                 /\ \E s \in LimitedSeq(Permutation(seq)) :
                      /\ \A i \in 1..Len(seq) :
                           (i < int.low \/ i > int.hi) => s[i] = seq[i]
                      /\ \A i \in int.low..int.hi : s[i] <= s[k]
                      /\ seq' = s
               /\ todo' = rest \cup {[low |-> int.low, hi |-> k],
                                     [low |-> k + 1, hi |-> int.hi]}
       /\ UNCHANGED orig
  /\ pc' = IF todo = {} THEN "done" ELSE "loop"

Stutter ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == Step \/ Stutter

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Step)
        /\ SF_vars(Stutter)

\* The algorithm is correct: termination produces a sorted permutation.
PCorrect ==
  (pc = "done") =>
    /\ Permutation(seq) = Permutation(orig)
    /\ \A i \in 1..(Len(seq) - 1) : seq[i] <= seq[i + 1]

\* An invariant tying the partitioning steps together.
Inv ==
  /\ \A int \in todo : int.low <= int.hi
  /\ Permutation(seq) = Permutation(orig)
  /\ \A i, j \in 1..MaxSeqLen :
        (i <= j /\ i \in {t.low : t \in todo} /\ j \in {t.hi : t \in todo})
          => seq[i] <= seq[j]

\* Weak fairness on the loop step ensures progress toward termination.
Termination == <>(pc = "done")

====