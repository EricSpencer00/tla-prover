---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

\* No identifier may be renamed here. The identifier set matches the .cfg
\* exactly: the constants Values, MaxSeqLen, Seq, the spec name Spec, the
\* init and next actions, the three invariants, and the termination
\* property. The spec follows the Quicksort example from Lamport's book.

CONSTANTS Values, MaxSeqLen, Seq

N == Len(Seq)

\* Permutations of the domain expressed as compositions with automorphisms
\* (bijections) of the index set 1..N.
Permutations ==
  {f \in [1..N -> 1..N] : \A x \in 1..N : \A y \in 1..N : f[x] = f[y] => x = y}

\* The partition operator is nondeterministic over all valid outcomes:
\* it may leave every element unchanged, or it may permute the interval
\* so that everything at or below the pivot index is no greater than
\* everything above it. Elements outside the interval are never moved.
Partition(s, lo, hi, p) ==
  {t \in Permutations :
     (t[lo] = lo /\ t[hi] = hi) /\ (\A i \in 1..N : (i < lo \/ i > hi) => s[t[i]] = s[i])
       /\ (\A a \in lo..p : \A b \in (p + 1)..hi : s[t[a]] <= s[t[b]])}

Domain == 1..N

\* Intervals are subsets of the domain, stored as sets of indices.
\* The "inverted" form is the record-interval style used by the book,
\* the set form is the set-theoretic style used in the invariant.
Intervals == SUBSET OF Domain
RecordIntervals == [lo : 1..N, hi : 1..N]
SetFromRec(r) == {i \in Domain : r.lo <= i /\ i <= r.hi}
RecFromSet(w) == CHOOSE r \in RecordIntervals : SetFromRec(r) = w

VARIABLES sequence, original, work, pc
vars == <<sequence, original, work, pc>>

TypeOK ==
  /\ sequence \in Seq(Domain)
  /\ original \in Seq(Domain)
  /\ work \subseteq Intervals
  /\ pc \in {"run", "done"}

Init ==
  /\ sequence = Seq
  /\ original = Seq
  /\ work = {Domain}
  /\ pc = "run"

\* One iteration of the sorting loop: either remove a singleton interval
\* or partition a larger one, nondeterministically picking the result.
Step ==
  /\ pc = "run"
  /\ work # {}
  /\ \E w \in work :
       /\ work' = work \ {w}
       /\ IF Cardinality(w) = 1
            THEN work'
            ELSE
              /\ \E p \in w :
                   /\ Cardinality(w) = 2 \/ p # CHOOSE x \in w : TRUE
                   /\ LET lo == CHOOSE x \in w : TRUE
                          hi == CHOOSE x \in w : TRUE
                          hi > lo
                          /\ work' = work' \cup {w \ {p}}
                          /\ work' = work' \cup {SetFromRec([lo |-> lo, hi |-> p])}
                          /\ work' = work' \cup {SetFromRec([lo |-> (p + 1), hi |-> hi])}
                     IN \E t \in Partition(sequence, lo, hi, p) :
                          sequence' = [i \in Domain |-> t[i]]
              /\ original' = original

Done ==
  /\ pc = "run"
  /\ work = {}
  /\ pc' = "done"
  /\ UNCHANGED <<sequence, original, work>>

Stall ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == Step \/ Done \/ Stall

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

\* Relative sortedness between intervals, expressed in both notations.
Inv ==
  /\ (\A x \in work : Cardinality(x) \in {0, 1})
  /\ (Cardinality(work) = N => work = Intervals)
  /\ (\A a \in work : \A b \in work :
       /\ (a # b /\ CHOOSE x \in Domain : a = x)
       /\ (\A x \in a, y \in b : x < y => sequence[x] <= sequence[y]))
  /\ (\A r \in RecordIntervals :
       /\ (\A a \in SetFromRec(r), b \in SetFromRec(r) : a < b => sequence[a] <= sequence[b]))

\* Permutation plus sortedness together give the final result.
PCorrect ==
  /\ (pc = "done" => Multiset(sequence) = Multiset(original))
  /\ (pc = "done" => \A i \in 1..(N - 1) : sequence[i] <= sequence[i + 1])

Termination == (pc = "run") ~> (pc = "done")

====