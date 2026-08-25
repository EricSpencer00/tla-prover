---- MODULE Quicksort ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Values, MaxSeqLen

(* --------------------------------------------------------------------- *)
(*  A finite version of Seq for model checking (replaces Seq)            *)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

(* --------------------------------------------------------------------- *)
VARIABLES seq, orig, work, pc

(* --------------------------------------------------------------------- *)
(*  Helper definitions                                                   *)
Intervs(s) == { [low |-> l, high |-> h] :
                 l \in 1..Len(s), h \in l..Len(s) }

Count(s, v) == Cardinality({ i \in 1..Len(s) : s[i] = v })

Permutation(s1, s2) == \A v \in Values : Count(s1, v) = Count(s2, v)

Sorted(s) == \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

(* --------------------------------------------------------------------- *)
(*  Initial state                                                       *)
Init ==
    /\ seq \in LimitedSeq(Values) \ { <<>> }
    /\ orig = seq
    /\ work = { [low |-> 1, high |-> Len(seq)] }
    /\ pc  = "Loop"

(* --------------------------------------------------------------------- *)
(*  Partition operator: all sequences that could result from a valid    *)
(*  partition of interval I around pivot piv                             *)
Partition(seq, I, piv) ==
    { s \in Seq(Values) :
        /\ Len(s) = Len(seq)
        /\ (\A j \in 1..Len(seq) :
              IF j \in I.low..I.high THEN s[j] \in Values ELSE s[j] = seq[j])
        /\ (\A j \in I.low..piv :
              \A k \in piv+1..I.high : s[j] <= s[k]) }

(* --------------------------------------------------------------------- *)
(*  One iteration of the sorting loop                                    *)
LoopStep ==
    /\ pc = "Loop"
    /\ work # {}
    /\ LET I == CHOOSE i \in work : TRUE
       IN
          IF I.low = I.high THEN
              /\ work' = work \ {I}
              /\ UNCHANGED <<seq, orig, pc>>
          ELSE
              /\ piv \in I.low .. I.high
              /\ seq' \in Partition(seq, I, piv)
              /\ lower == [low |-> I.low,  high |-> piv - 1]
              /\ upper == [low |-> piv + 1, high |-> I.high]
              /\ work' = (work \ {I})
                         \cup (IF lower.low <= lower.high THEN {lower} ELSE {})
                         \cup (IF upper.low <= upper.high THEN {upper} ELSE {})
              /\ UNCHANGED orig
              /\ pc' = "Loop"

(* --------------------------------------------------------------------- *)
(*  Termination when no intervals remain                                 *)
Terminate ==
    /\ pc = "Loop"
    /\ work = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<seq, orig, work>>

(* --------------------------------------------------------------------- *)
(*  Stuttering after termination                                          *)
Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<seq, orig, work, pc>>

(* --------------------------------------------------------------------- *)
Next == LoopStep \/ Terminate \/ Stutter

vars == <<seq, orig, work, pc>>

(* --------------------------------------------------------------------- *)
(*  Specification                                                       *)
Spec == Init /\ [][Next]_vars

(* --------------------------------------------------------------------- *)
(*  Invariants                                                          *)
TypeOK ==
    /\ seq \in LimitedSeq(Values) \ { <<>> }
    /\ orig = seq
    /\ work \subseteq Intervs(seq)
    /\ pc \in {"Loop", "Done"}

Inv == /\ TypeOK
       /\ Permutation(seq, orig)

PCorrect == (pc = "Done") => (Sorted(seq) /\ Permutation(seq, orig))

(* --------------------------------------------------------------------- *)
(*  Liveness property (termination)                                      *)
Termination == <> (pc = "Done")

====