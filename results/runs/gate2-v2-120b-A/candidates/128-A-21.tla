---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets

(***************************************************************************)
(*  Constants (provided by the .cfg file)                                  *)
(***************************************************************************)
CONSTANTS Values, MaxSeqLen, Seq

(***************************************************************************)
(*  Types and derived constants                                            *)
(***************************************************************************)
\* Domain of indices for sequences up to MaxSeqLen
Idx == 1 .. MaxSeqLen

\* Set of all sequences of length at most MaxSeqLen drawn from Values
SeqSet == { s \in Seq(Values) : Len(s) <= MaxSeqLen }

\* Helper to talk about intervals (contiguous ranges of indices)
Interval == [low : Nat, high : Nat]

IntervalOK(iv) == /\ iv.low \in Idx
                  /\ iv.high \in Idx
                  /\ iv.low <= iv.high

\* Non‑empty work‑set of intervals
WorkSet == SUBSET { iv \in [low: Nat, high: Nat] : IntervalOK(iv) }

(***************************************************************************)
(*  Variables                                                              *)
(***************************************************************************)
VARIABLES a, a0, work, pc

(***************************************************************************)
(*  Initialization                                                         *)
(***************************************************************************)
Init ==
  /\ a \in SeqSet
  /\ a0 = a
  /\ Len(a) > 0
  /\ work = { [low |-> 1, high |-> Len(a)] }
  /\ pc = "Loop"

(***************************************************************************)
(*  Utilities                                                               *)
(***************************************************************************)
\* All indices of a sequence a
Indices(a) == 1 .. Len(a)

\* Permutation relation: b is a permutation of a
Permutation(a, b) ==
  /\ Len(a) = Len(b)
  /\ \A i \in Indices(a) : \E j \in Indices(b) : b[j] = a[i]

\* Sortedness predicate
Sorted(a) == \A i, j \in Indices(a) : i < j => a[i] <= a[j]

\* Nondeterministic partition respecting the pivot
Partition(a, low, high, p) ==
  LET leftInds  == { i \in low .. p }  IN
  LET rightInds == { i \in p+1 .. high } IN
  /\ p \in low .. high
  /\ \A i \in leftInds, j \in rightInds : a[i] <= a[j]
  /\ \A i \in low .. high : a[i] = a[i]   \* elements stay within interval (no change)
  /\ a' = a                               \* placeholder; actual new sequence chosen below
  /\ \E b \in SeqSet :
        /\ Len(b) = Len(a)
        /\ \A i \in Indices(a) :
              IF i \in low .. high THEN b[i] = a[i] ELSE b[i] = a[i]
        /\ \A i \in leftInds, j \in rightInds : b[i] <= b[j]

(***************************************************************************)
(*  Main action (one loop iteration)                                       *)
(***************************************************************************)
Loop ==
  /\ pc = "Loop"
  /\ work # {}
  /\ \E iv \in work :
        LET low  == iv.low
            high == iv.high
        IN
        IF low = high THEN
          /\ work' = work \ { iv }
          /\ UNCHANGED <<a, a0>>
        ELSE
          /\ \E p \in low .. high :
                LET left  == [low |-> low , high |-> p]
                    right == [low |-> p+1, high |-> high]
                IN
                /\ a' \in SeqSet
                /\ Len(a') = Len(a)
                /\ \A i \in Indices(a) :
                      IF i \in low .. high THEN a'[i] = a[i] ELSE a'[i] = a[i]
                /\ \A i \in low .. p, j \in p+1 .. high : a'[i] <= a'[j]
                /\ work' = (work \ { iv }) \cup { left, right }
          /\ a0' = a0
      /\ pc' = "Loop"

\* Stuttering step after termination
Terminate ==
  /\ pc = "Done"
  /\ UNCHANGED <<a, a0, work, pc>>

Next ==
  \/ Loop
  \/ ( /\ pc = "Loop"
       /\ work = {}
       /\ pc' = "Done"
       /\ UNCHANGED <<a, a0, work>> )
  \/ Terminate

(***************************************************************************)
(*  Specification                                                          *)
(***************************************************************************)
Spec == Init /\ [][Next]_<<a, a0, work, pc>>

(***************************************************************************)
(*  Invariant (partial correctness)                                        *)
(***************************************************************************)
Inv ==
  /\ a0 \in SeqSet
  /\ a \in SeqSet
  /\ Len(a) = Len(a0)
  /\ Permutation(a0, a)
  /\ Sorted(a) => pc = "Done"

(***************************************************************************)
(*  Type OK invariant                                                       *)
(***************************************************************************)
TypeOK ==
  /\ a \in SeqSet
  /\ a0 \in SeqSet
  /\ work \subseteq { iv \in [low: Nat, high: Nat] : IntervalOK(iv) }
  /\ pc \in {"Loop", "Done"}

(***************************************************************************)
(*  Safety property (alias for Inv)                                         *)
(***************************************************************************)
PCorrect == Inv

(***************************************************************************)
(*  Liveness property (termination)                                         *)
(***************************************************************************)
Termination == <> (pc = "Done")

=============================================================================