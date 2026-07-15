---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen, Seq

(*-------------------------------------------------------------------*)
(* Type definitions *)
Idx == 1 .. MaxSeqLen

SeqDomain == { i \in Idx : TRUE }

SeqOfVals == [i \in SeqDomain -> Values]

Interval == [low : Idx, high : Idx]  \* low <= high

Intervals == SUBSET Interval

(*-------------------------------------------------------------------*)
(* Helper definitions *)

\* Orders an interval from low to high
IntervalIndices(i) == i.low .. i.high

\* Returns the union of all indices covered by a set of intervals
CoveredIndices(S) == UNION { IntervalIndices(i) : i \in S }

Sorted(s) ==
  \A i,j \in SeqDomain :
    (i < j) => s[i] <= s[j]

(* Permutation definition: there exists a bijection on indices that
   reorders the sequence. *)
Permutes(s, t) ==
  \E f \in [SeqDomain -> SeqDomain] :
    (\A i,j \in SeqDomain : f[i] = f[j] => i = j) /\   \* injective (hence bijective on finite set)
    (\A i \in SeqDomain : t[i] = s[f[i]])

ValidInterval(i) ==
  /\ i.low \in Idx
  /\ i.high \in Idx
  /\ i.low <= i.high

(*-------------------------------------------------------------------*)
(* Variables *)
VARIABLES seq, orig, work, pc

(*-------------------------------------------------------------------*)
(* Initial state *)

Init ==
  /\ seq = Seq
  /\ orig = Seq
  /\ work = { [low |-> 1, high |-> Len(seq)] }
  /\ pc = "Loop"

(*-------------------------------------------------------------------*)
(* Actions *)

Terminate ==
  /\ work = {}
  /\ pc' = "Done"
  /\ UNCHANGED <<seq, orig, work>>

StutterAfterDone ==
  /\ pc = "Done"
  /\ UNCHANGED <<seq, orig, work, pc>>

(* One iteration of the sorting loop *)
Loop ==
  /\ pc = "Loop"
  /\ IF work = {}
        THEN /\ pc' = "Done"
             /\ UNCHANGED <<seq, orig, work>>
        ELSE
          /\ \E i \in work :
               LET low == i.low IN
               LET high == i.high IN
               IF low = high
                 THEN /\ work' = work \ {i}
                      /\ UNCHANGED <<seq, orig>>
                 ELSE
                   LET pivot \in low .. high IN
                   /\ low <= pivot <= high
                   /\ let lower == [low |-> low, high |-> pivot - 1] in
                      let upper == [low |-> pivot + 1, high |-> high] in
                      /\ lower.low <= lower.high \/ lower.low > lower.high  \* lower may be empty
                      /\ upper.low <= upper.high \/ upper.low > upper.high   \* upper may be empty
                      /\ \E newSeq \in SeqOfVals :
                           /\ (\A j \in SeqDomain :
                                 (j < low) \/ (j > high) => newSeq[j] = seq[j])
                           /\ (\A j \in low .. pivot :
                                 newSeq[j] <= newSeq[pivot])
                           /\ (\A j \in pivot+1 .. high :
                                 newSeq[pivot] <= newSeq[j])
                           /\ seq' = newSeq
                      /\ work' = (work \ {i}) \cup
                                 (IF lower.low <= lower.high THEN {lower} ELSE {}) \cup
                                 (IF upper.low <= upper.high THEN {upper} ELSE {})
          /\ pc' = "Loop"

Next ==
  \/ Loop
  \/ Terminate
  \/ StutterAfterDone

(*-------------------------------------------------------------------*)
(* Specification *)

Init == Init
Next == Next

Spec == Init /\ [][Next]_<<seq, orig, work, pc>>

(*-------------------------------------------------------------------*)
(* Invariant definitions *)

PCorrect ==
  /\ (pc = "Done") => /\ Sorted(seq)
                       /\ Permutes(orig, seq)
  /\ (pc = "Loop") => Permutes(orig, seq)

TypeOK ==
  /\ seq \in SeqOfVals
  /\ orig \in SeqOfVals
  /\ work \subseteq Intervals
  /\ pc \in {"Loop", "Done"}

Inv == PCorrect /\ TypeOK

(*-------------------------------------------------------------------*)
(* Liveness property *)

Termination == <> (pc = "Done")

====