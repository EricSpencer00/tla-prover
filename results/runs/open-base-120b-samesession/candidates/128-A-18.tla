---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen

(* ---------------------------------------------------------------------- *)
(*  A finite set of non‑empty sequences over Values, bounded by MaxSeqLen   *)
(* ---------------------------------------------------------------------- *)
LimitedSeq == { s \in Seq(Values) : Len(s) > 0 /\ Len(s) <= MaxSeqLen }

VARIABLES seq, orig, work, pc

vars == <<seq, orig, work, pc>>

(* ---------------------------------------------------------------------- *)
(*  Helper definitions                                                   *)
(* ---------------------------------------------------------------------- *)

Indices == 1..Len(seq)

IntervalIndices(I) == { i \in Indices : I[1] <= i /\ i <= I[2] }

AllIntervals == { <<l, h>> \in Nat \X Nat :
                    1 <= l /\ h <= Len(seq) /\ l <= h }

IsPermutation(s1, s2) ==
  \A v \in Values :
    Cardinality({ i \in DOMAIN s1 : s1[i] = v }) =
    Cardinality({ i \in DOMAIN s2 : s2[i] = v })

IsSorted(s) ==
  \A i, j \in DOMAIN s : i < j => s[i] <= s[j]

(* ---------------------------------------------------------------------- *)
(*  Type correctness                                                     *)
(* ---------------------------------------------------------------------- *)
TypeOK ==
  /\ seq \in Seq(Values)
  /\ orig \in Seq(Values)
  /\ Len(seq) > 0
  /\ Len(seq) <= MaxSeqLen
  /\ work \subseteq AllIntervals
  /\ pc \in {"Loop", "Done"}

(* ---------------------------------------------------------------------- *)
(*  Invariant used in the proof                                          *)
(* ---------------------------------------------------------------------- *)

ProcessedIndices ==
  Indices \ UNION { IntervalIndices(I) : I \in work }

SortedProcessed ==
  \A i, j \in ProcessedIndices : i < j => seq[i] <= seq[j]

Inv ==
  /\ TypeOK
  /\ IsPermutation(seq, orig)
  /\ SortedProcessed

(* ---------------------------------------------------------------------- *)
(*  Initial state                                                         *)
(* ---------------------------------------------------------------------- *)
Init ==
  /\ seq \in LimitedSeq
  /\ orig = seq
  /\ work = { <<1, Len(seq)>> }
  /\ pc = "Loop"

(* ---------------------------------------------------------------------- *)
(*  One step of the quick‑sort algorithm                                   *)
(* ---------------------------------------------------------------------- *)
Next ==
  \/ /\ pc = "Loop"
     /\ IF work = {}
        THEN /\ pc' = "Done"
             /\ UNCHANGED <<seq, orig, work>>
        ELSE
          \E I \in work :
            LET low == I[1] IN
            LET high == I[2] IN
            IF low = high
            THEN /\ work' = work \ {I}
                 /\ UNCHANGED <<seq, orig>>
                 /\ pc' = "Loop"
            ELSE
              \E p \in low..high :
                \E newSeq \in Seq(Values) :
                  /\ Len(newSeq) = Len(seq)
                  /\ (\A i \in Indices :
                       IF i \notin IntervalIndices(I) THEN newSeq[i] = seq[i] ELSE TRUE)
                  /\ (\A i \in low..p, j \in p+1..high : newSeq[i] <= newSeq[j])
                  /\ IsPermutation(newSeq, seq)
                /\ seq' = newSeq
                /\ work' = (work \ {I}) \cup
                          (IF low <= p-1 THEN {<<low, p-1>>} ELSE {}) \cup
                          (IF p+1 <= high THEN {<<p+1, high>>} ELSE {})
                /\ pc' = "Loop"
  \/ /\ pc = "Done"
     /\ UNCHANGED vars

(* ---------------------------------------------------------------------- *)
(*  Specification                                                         *)
(* ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_vars

(* ---------------------------------------------------------------------- *)
(*  Safety invariants                                                     *)
(* ---------------------------------------------------------------------- *)
PCorrect ==
  /\ pc = "Done" => (IsSorted(seq) /\ IsPermutation(seq, orig))

(* ---------------------------------------------------------------------- *)
(*  Liveness property                                                     *)
(* ---------------------------------------------------------------------- *)
Termination == <> (pc = "Done")

====