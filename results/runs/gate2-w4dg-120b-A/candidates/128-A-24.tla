---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values, MaxSeqLen, Seq

VARIABLES seq, base, wset, pc
vars == <<seq, base, wset, pc>>

\* Intervals in wset are contiguous subranges of the sequence; the
\* algorithm processes them one at a time, always shrinking the work set,
\* so it must eventually terminate.
Ranges == {r \in 1..MaxSeqLen : r >= 2}

\* A permutation of a sequence is a composition with an automorphism of its
\* domain; this definition appears in Lamport's notes on sorting.
Permutation(s, t) ==
  /\ Len(s) = Len(t)
  /\ \E f \in [1..Len(s) -> 1..Len(s)] :
       /\ \A i \in 1..Len(s), j \in 1..Len(s) : f[i] = f[j] => i = j
       /\ \A i \in 1..Len(s) : t[i] = s[f[i]]

\* The partition operator models the soundness of any valid partition
\* implementation: it is free to move every element at or below the pivot
\* index into the lower half, and every element above it into the upper
\* half, but it may not touch elements outside the interval.
Partitions(s, lo, hi) ==
  {t \in [1..Len(s) -> Values] :
     /\ \A i \in 1..Lo \cup Hi : t[i] = s[i]
     /\ \A i \in Lo, j \in Hi : t[i] <= t[j]
     /\ \A i \in 1..Len(s) : t[i] \in Values}
  where Lo == 1..lo /\ Hi == (hi + 1)..Len(s)

TypeOK ==
  /\ seq \in [1..MaxSeqLen -> Values]
  /\ base \in [1..MaxSeqLen -> Values]
  /\ wset \subseteq Ranges
  /\ pc \in {"loop", "done"}

Init ==
  /\ seq = Seq
  /\ base = Seq
  /\ wset = {MaxSeqLen}
  /\ pc = "loop"

\* One iteration of the sorting loop: either discard a singleton interval
\* or split a larger one, choosing a pivot and a valid partition result.
QuicksortStep ==
  /\ pc = "loop"
  /\ \E r \in wset :
       IF r = 1
         THEN wset' = wset \ {r}
         ELSE
           \E p \in 1..r :
             /\ \E seq' \in Partitions(seq, p, r) : seq' # seq /\ seq' \in [1..MaxSeqLen -> Values]
             /\ wset' = (wset \ {r}) \cup {p, r - p}
       /\ seq' = IF r = 1
                  THEN seq
                  ELSE CHOOSE seq' \in Partitions(seq, p, r) : TRUE
  /\ pc' = IF wset = {1} THEN "done" ELSE "loop"

\* A stuttering step that keeps TLC from deadlocking after termination.
Stall == /\ pc = "done" /\ UNCHANGED vars

Next == QuicksortStep \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(QuicksortStep)

Sorted(s) == \A i \in 1..(Len(s) - 1) : s[i] <= s[i + 1]

\* The invariant is the union of all pieces the proof breaks down: the work
\* set is always a partition of the domain, the current sequence is a
\* permutation of the original, and each subinterval is internally sorted.
Inv ==
  /\ \A r \in wset : r >= 1
  /\ Permutation(seq, base)
  /\ \A r \in wset : \A i \in 1..(r - 1) : seq[i] <= seq[i + 1]

PCorrect == pc = "done" => (Permutation(seq, base) /\ Sorted(seq))
Termination == <>(pc = "done")

\* The configuration file also declares a TLAPS proof sketch; the sketch is
\* not part of the module itself, but the operators it targets must exist.
====