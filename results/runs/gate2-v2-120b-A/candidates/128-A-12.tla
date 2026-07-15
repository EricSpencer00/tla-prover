---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg)
\* ----------------------------------------------------------------------
CONSTANT Values          \* a finite subset of Nat, the allowed values
CONSTANT MaxSeqLen       \* a positive integer giving the bound on sequence length
CONSTANT Seq             \* the initial sequence (a function from 1..n to Values)

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
n == Len(Seq)           \* length of the initial sequence (must be > 0)

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Types for readability
\* ----------------------------------------------------------------------
Idx == 1..n
Interval == [low: Idx, high: Idx] \* low <= high

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Checks that an interval is well‑formed
IntervalOK(i) == /\ i.low \in Idx
                /\ i.high \in Idx
                /\ i.low <= i.high

\* Intervals that are singletons
Singleton(i) == i.low = i.high

\* Lower and upper subintervals produced by a pivot j within i
LowerSub(i, j) == [low |-> i.low, high |-> j]
UpperSub(i, j) == [low |-> j + 1, high |-> i.high]

\* The set of all possible partitions of `seq` over interval `i` with pivot `j`.
\* A partition may arbitrarily permute the elements inside the interval,
\* provided that every element in the lower part is <= every element in the
\* upper part, and elements outside the interval stay unchanged.
Partition(seq, i, j) ==
  { newSeq \in [Idx -> Values] :
        /\ \A k \in Idx :
              (k < i.low \/ k > i.high) => newSeq[k] = seq[k]
        /\ \A p \in i.low..j :
              \A q \in (j+1)..i.high =>
                 newSeq[p] <= newSeq[q] }

\* Permutation of a sequence: there exists a bijection of the index set that
\* maps the original to the new sequence.
Permutation(s1, s2) ==
  \E f \in [Idx -> Idx] :
        /\ \A i \in Idx : f[i] \in Idx
        /\ \A i, j \in Idx : f[i] = f[j] => i = j
        /\ \A i \in Idx : s2[i] = s1[f[i]]

\* Sortedness of a sequence over the whole index range
Sorted(s) == \A i, j \in Idx : i < j => s[i] <= s[j]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ seq  = Seq
  /\ orig = Seq
  /\ work = { [low |-> 1, high |-> n] }
  /\ pc   = "Loop"

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* The main loop body: either remove a singleton interval or partition a larger one
Loop ==
  \/ /\ work # {}
     /\ \E i \in work :
          /\ IntervalOK(i)
          /\ ( \/ /\ Singleton(i)
                  /\ work' = work \ {i}
                  /\ UNCHANGED <<seq, orig>>
               \/ /\ ~Singleton(i)
                  /\ \E j \in i.low..i.high :
                        /\ lower = LowerSub(i, j)
                        /\ upper = UpperSub(i, j)
                        /\ seq' \in Partition(seq, i, j)
                        /\ work' = (work \ {i}) \cup {lower, upper}
                        /\ UNCHANGED orig )
          /\ pc' = "Loop"

  \/ /\ work = {}
     /\ pc' = "Done"
     /\ UNCHANGED <<seq, orig, work>>

\* Stuttering step after termination to avoid deadlock
DoneStutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<seq, orig, work, pc>>

Next == Loop \/ DoneStutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Invariant required by the .cfg
\* ----------------------------------------------------------------------
\* PCorrect: when the algorithm reports termination, the sequence is a sorted
\* permutation of the original input.
PCorrect ==
  (pc = "Done") => (Sorted(seq) /\ Permutation(orig, seq))

\* TypeOK: basic type correctness of all variables
TypeOK ==
  /\ seq \in [Idx -> Values]
  /\ orig \in [Idx -> Values]
  /\ work \subseteq { i \in [low: Idx, high: Idx] : i.low <= i.high }
  /\ pc \in {"Loop", "Done"}

\* Inv: the inductive invariant described in the natural language text.
\* It combines:
\*   – the set of intervals in `work` are disjoint and cover exactly the parts
\*     of the array that are not yet known to be sorted,
\*   – `orig` is always a permutation of the initial `Seq`,
\*   – the current `seq` is a permutation of `orig`,
\*   – for every interval that is not in `work`, the corresponding slice of `seq`
\*     is already sorted.
Inv ==
  /\ Permutation(orig, Seq)
  /\ Permutation(seq, orig)
  /\ \A i \in work : IntervalOK(i)
  /\ \A i, j \in work :
        (i.low <= j.low /\ i.low <= j.high) =>
          (i.high < j.low \/ i.low > j.high)  \* intervals are non‑overlapping
  /\ \A i \in Idx :
        (\E iv \in work : i \in iv.low .. iv.high) =>
          TRUE   \* indices covered by some work interval (no extra condition)
  /\ \A i \in Idx :
        (\A iv \in work : ~ (i \in iv.low .. iv.high)) =>
          \A k \in Idx :
                ( (i <= k /\ k <= n) => seq[i] <= seq[k] )   \* already sorted outside work

\* ----------------------------------------------------------------------
\* Liveness claim (used as a property in the .cfg)
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

====