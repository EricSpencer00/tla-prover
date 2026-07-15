---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(*  Constants                                                             *)
(*  Values   : the set of integer values that may appear in the sequence   *)
(*  MaxSeqLen: the maximum length of the sequence (used in the companion   *)
(*             configuration module)                                      *)
(*  Seq      : a function that maps each n \in 1..MaxSeqLen to an integer  *)
(*             in Values; the length of the actual sequence is the first *)
(*             n such that the rest of the entries are a dummy value.     *)
(***************************************************************************)
CONSTANTS Values, MaxSeqLen, Seq

(***************************************************************************)
(*  State variables                                                       *)
(*  curSeq   : the current sequence being sorted (a sequence of Values)   *)
(*  origSeq  : a copy of the initial sequence for permutation checking     *)
(*  workSet  : a set of intervals still to be processed; each interval is  *)
(*            a pair <<low, high>> with 1 <= low <= high <= Len(curSeq)   *)
(*  pc       : program counter, either "Loop" or "Done"                    *)
(***************************************************************************)
VARIABLES curSeq, origSeq, workSet, pc

(***************************************************************************)
(*  Helper definitions                                                    *)
(*  Len(s)     : the length of a sequence s (first index where the dummy   *)
(*               value appears, or 1 + MaxSeqLen if none)                *)
(*  Intervals : the set of all possible intervals over 1..Len(curSeq)     *)
(*  Partitions: the set of all sequences that are valid partitions of the *)
(*              current sequence for a given interval and pivot            *)
(*  Permutes  : the set of all permutations of a sequence that preserve    *)
(*              the multiset of elements                                 *)
(***************************************************************************)

Len(s) == 
    CHOOSE n \in 1..MaxSeqLen + 1 : 
        (s[n] = s[MaxSeqLen]) \/ n = MaxSeqLen + 1

Intervals == { <<i, j>> \in [1..MaxSeqLen] \X [1..MaxSeqLen] : i <= j }

(* A partition leaves elements outside [low,high] unchanged, and guarantees
   that every element whose final index is <= pivotIdx is <= every element
   whose final index is > pivotIdx.  The concrete values of indices are not
   important; we only need to express that such a sequence exists. *)
Partitions(cur, low, high, pivotIdx) ==
    { new \in Seq :
        /\ \A k \in 1..low-1 : new[k] = cur[k]
        /\ \A k \in high+1..Len(cur) : new[k] = cur[k]
        /\ \A i \in low..pivotIdx : \A j \in pivotIdx+1..high :
               new[i] <= new[j] }

(* Permutation preserving the multiset of elements *)
Permutes(s) == 
    { t \in Seq :
        \A v \in Values : 
            Cardinality({ i \in 1..Len(s) : s[i] = v }) =
            Cardinality({ i \in 1..Len(t) : t[i] = v }) }

(* Type invariant for readability; not the same as the safety invariant *)
TypeOK == 
    /\ curSeq \in Seq
    /\ origSeq \in Seq
    /\ workSet \subseteq Intervals
    /\ pc \in {"Loop", "Done"}

(***************************************************************************)
(*  Initial predicate                                                     *)
(***************************************************************************)
Init ==
    /\ curSeq \in Seq
    /\ origSeq = curSeq
    /\ workSet = { <<1, Len(curSeq)>> }
    /\ pc = "Loop"

(***************************************************************************)
(*  Main action: one iteration of the sorting loop                        *)
(***************************************************************************)
Loop ==
    \/ \E intv \in workSet :
          LET low == intv[1] IN
          LET high == intv[2] IN
          IF low = high THEN
             /\ workSet' = workSet \ {intv}
             /\ UNCHANGED <<curSeq, origSeq, pc>>
          ELSE
             /\ \E pivotIdx \in low..high :
                /\ \E newSeq \in Partitions(curSeq, low, high, pivotIdx) :
                    /\ curSeq' = newSeq
                    /\ workSet' = (workSet \ {intv}) \cup { <<low, pivotIdx>>, <<pivotIdx+1, high>> }
                    /\ pc' = "Loop"
                    /\ UNCHANGED origSeq
    \/ /\ workSet = {}
       /\ pc = "Done"
       /\ UNCHANGED <<curSeq, origSeq, workSet>>

(***************************************************************************)
(*  Stuttering step after termination                                      *)
(***************************************************************************)
Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<curSeq, origSeq, workSet, pc>>

Next == Loop \/ Stutter

(***************************************************************************)
(*  Specification formula                                                 *)
(***************************************************************************)
Spec == Init /\ [][Next]_<<curSeq, origSeq, workSet, pc>>

(***************************************************************************)
(*  Safety invariant (partial correctness)                                *)
(*  When pc = "Done", curSeq is a permutation of origSeq and is sorted.   *)
(***************************************************************************)
PCorrect ==
    (pc = "Done") =>
        /\ curSeq \in Permutes(origSeq)
        /\ \A i, j \in 1..Len(curSeq) : i < j => curSeq[i] <= curSeq[j]

(***************************************************************************)
(*  Additional invariants (optional but useful for debugging)             *)
(***************************************************************************)
Inv == 
    /\ workSet \subseteq Intervals
    /\ \A intv \in workSet : intv[1] <= intv[2]
    /\ Len(curSeq) = Len(origSeq)

(***************************************************************************)
(*  Liveness property (termination)                                       *)
(***************************************************************************)
Termination == <>[](pc = "Done")

=============================================================================