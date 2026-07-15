---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen, Seq

VARIABLES seq, orig, work, pc

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Idx == 1 .. MaxSeqLen

SeqOfVals == [i \in Idx |-> Values]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Interval == [lo : Idx, hi : Idx] \* lo <= hi

Singleton(i) == [lo |-> i, hi |-> i]

\* All indices of a sequence (non‑empty by assumption)
AllIdx(s) == DOMAIN s

\* Permutation predicate (exists a bijection on AllIdx that rearranges s to t)
Permutation(s, t) ==
  \E f \in [AllIdx(s) -> AllIdx(s)] :
    /\ \A i \in AllIdx(s) : s[f[i]] = t[i]
    /\ \A i, j \in AllIdx(s) : f[i] = f[j] => i = j

\* Sortedness predicate (non‑decreasing order)
Sorted(s) ==
  \A i, j \in AllIdx(s) : i < j => s[i] <= s[j]

\* Partition operation: nondeterministically pick a new sequence that
\*   – leaves elements outside the interval unchanged,
\*   – respects the pivot ordering,
\*   – is a permutation of the original on the whole domain.
Partition(old, int, pivot) ==
  \E new \in SeqOfVals :
    /\ \A i \in Idx :
         (i < int.lo \/ i > int.hi) => new[i] = old[i]
    /\ \A i, j \in Idx :
         (int.lo <= i /\ i <= pivot /\ pivot < j /\ j <= int.hi) => new[i] <= new[j]
    /\ Permutation(old, new)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ seq = Seq
  /\ orig = seq
  /\ work = { [lo |-> 1, hi |-> Len(seq)] }
  /\ pc = "Loop"

\* ----------------------------------------------------------------------
\* Main action (one iteration of the loop)
\* ----------------------------------------------------------------------
Step ==
  \/ /\ pc = "Loop"
     /\ work # {}
     /\ \E int \in work :
          IF int.lo = int.hi THEN
            /\ work' = work \ {int}
            /\ UNCHANGED <<seq, orig, pc>>
          ELSE
            /\ \E pivot \in int.lo .. int.hi :
                 /\ seq' = Partition(seq, int, pivot)
                 /\ work' = (work \ {int}) \cup { [lo |-> int.lo, hi |-> pivot],
                                                [lo |-> pivot+1, hi |-> int.hi] }
                 /\ pc' = "Loop"
  \/ /\ pc = "Loop"
     /\ work = {}
     /\ pc' = "Done"
     /\ UNCHANGED <<seq, orig, work>>

\* Stuttering step after termination
Terminated ==
  /\ pc = "Done"
  /\ UNCHANGED <<seq, orig, work, pc>>

Next == Step \/ Terminated

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
PCorrect ==
  (pc = "Done" => /\ Sorted(seq) /\ Permutation(orig, seq))
  /\ (pc = "Loop" => TRUE)

TypeOK ==
  /\ seq \in SeqOfVals
  /\ orig \in SeqOfVals
  /\ work \subseteq { int \in Interval : int.lo <= int.hi /\ int.lo >= 1 /\ int.hi <= Len(seq) }
  /\ pc \in {"Loop", "Done"}

Inv == 
  /\ TypeOK
  /\ \A int \in work : /\ int.lo >= 1 /\ int.hi <= Len(seq)
                     /\ int.lo <= int.hi

\* ----------------------------------------------------------------------
\* Liveness property (termination)
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

====