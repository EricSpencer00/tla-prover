---- MODULE Quicksort ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Values, MaxSeqLen

\* The original Quicksort example from Lamport's book used the unbounded
\* Seq operator from the Sequences module. For model checking we need a
\* finite replacement that enumerates exactly the sequences up to a bound.
\* The .cfg file substitutes LimitedSeq for Seq, so we define LimitedSeq
\* here, reusing the Seq definition but capping the index range.
LimitedSeq(S) ==
  /\ DOMAIN~S \subseteq 1..MaxSeqLen
  /\ S \in [1..MaxSeqLen -> Values]

\* Sequences of the same length with exactly the same set of elements are
\* permutations of each other; the domain automorphism is implicit in that.
Permutations(s, t) ==
  \E f \in [DOMAIN s -> DOMAIN s] :
    /\ \A i \in DOMAIN s : s[i] = t[f[i]]
    /\ \A a, b \in DOMAIN s : f[a] = f[b] => a = b

Indices(S) == DOMAIN S

\* The partition operator is the nondeterministic core of the spec: the
\* chosen new version of the sequence is any permutation that leaves
\* everything outside the interval untouched while placing every element
\* on or below the pivot index no greater than every element above it.
Partition(S, interval, piv) ==
  {R \in [Indices(S) -> Values] :
     /\ \A i \in Indices(S) \ (i < interval[1] \/ i > interval[2]) : R[i] = S[i]
     /\ \A i \in interval[1]..piv, j \in piv+1..interval[2] : R[i] <= R[j]}

Low(i, j) == <<i, j>>
Src(i, j) == i
Dst(i, j) == j

VARIABLES seq, orig, todo, pc

vars == <<seq, orig, todo, pc>>

TypeOK ==
  /\ seq \in [Indices(seq) -> Values]
  /\ orig \in [Indices(seq) -> Values]
  /\ todo \subseteq (Nat \X Nat)
  /\ pc \in {"Loop", "Done"}

Init ==
  /\ seq \in LimitedSeq(Values)
  /\ orig = seq
  /\ todo = {Low(1, Len(seq))}
  /\ pc = "Loop"

\* One iteration of the sorting loop: pick an interval and either drop it
\* (a singleton) or split it around a pivot, choosing a valid partition.
Step ==
  \/ \E interval \in todo :
       /\ Len(interval) >= 2
       /\ \E piv \in interval[1]..interval[2] :
            \E newSeq \in Partition(seq, interval, piv) :
              /\ seq' = newSeq
              /\ todo' = (todo \ {interval}) \cup {Low(interval[1], piv), Low(piv+1, interval[2])}
       /\ pc' = "Loop"
       /\ UNCHANGED orig
  \/ \E interval \in todo :
       /\ Len(interval) = 1
       /\ todo' = todo \ {interval}
       /\ UNCHANGED <<seq, orig, pc>>
  \/ (todo = {} /\ pc = "Loop" /\ pc' = "Done" /\ UNCHANGED <<seq, orig, todo>>)

Next == Step

\* A stuttering step so the model never gets stuck once done.
Quiesce ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Spec == Init /\ [][Step]_vars /\ WF_vars(Quiesce)

Sorted == \A i \in 1..(Len(seq) - 1) : seq[i] <= seq[i + 1]

PCorrect ==
  pc = "Done" => (Permutations(seq, orig) /\ Sorted)

\* The full invariant is a conjunction of three pieces; a named operator
\* is used so each conjunct can be tracked individually in the proof.
Inv ==
  /\ \A interval \in todo :
       /\ interval[1] <= interval[2]
       /\ interval[2] <= Len(seq)
  /\ Permutations(seq, orig)
  /\ \A interval \in todo :
       Len(interval) >= 2 =>
         \A i \in interval[1]..(interval[2] - 1) : seq[i] <= seq[i + 1]

Termination == <>(pc = "Done")

SpecIFICATION Spec
INVARIANTS PCorrect, TypeOK, Inv
PROPERTIES Termination
====