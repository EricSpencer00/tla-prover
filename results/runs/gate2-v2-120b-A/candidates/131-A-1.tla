---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

(*---------------------------------------------------------------------*)
(*  Constants                                                          *)
(*---------------------------------------------------------------------*)
CONSTANT Value

(*---------------------------------------------------------------------*)
(*  State variables                                                    *)
(*---------------------------------------------------------------------*)
VARIABLES seq, i, candidate, count, maj

(*---------------------------------------------------------------------*)
(*  Derived sets                                                       *)
(*---------------------------------------------------------------------*)
Pos  == 0 .. Len(seq) - 1
PosAfter(i) == i + 1 .. Len(seq) - 1

(*---------------------------------------------------------------------*)
(*  Helper definitions                                                 *)
(*---------------------------------------------------------------------*)
(* Number of occurrences of v in positions 0..j (inclusive) *)
OccBefore(v, j) == Cardinality({ p \in 0..j : seq[p] = v })

(*---------------------------------------------------------------------*)
(*  Initial state                                                      *)
(*---------------------------------------------------------------------*)
Init ==
    /\ seq \in Seq(Value)                     \* input sequence
    /\ i = 0
    /\ candidate \in Value
    /\ count = 0
    /\ maj = 0

(*---------------------------------------------------------------------*)
(*  Main algorithm step                                                *)
(*---------------------------------------------------------------------*)
AlgoStep ==
    /\ i < Len(seq)
    /\ LET x == seq[i] IN
       IF count = 0 THEN
          /\ candidate' = x
          /\ count' = 1
       ELSE IF candidate = x THEN
          /\ count' = count + 1
          /\ UNCHANGED candidate
       ELSE
          /\ count' = count - 1
          /\ UNCHANGED candidate
    /\ i' = i + 1
    /\ UNCHANGED << seq, maj >>

(*---------------------------------------------------------------------*)
(*  Optional second pass to compute the number of occurrences of the   *)
(*  current candidate (needed for the correctness invariant).          *)
(*---------------------------------------------------------------------*)
CountMajStep ==
    /\ i = Len(seq)                \* start of second pass
    /\ maj < Len(seq)
    /\ maj' = maj + 1
    /\ UNCHANGED << seq, i, candidate, count >>

(*---------------------------------------------------------------------*)
(*  Stuttering step after both passes are finished                     *)
(*---------------------------------------------------------------------*)
Done ==
    /\ i = Len(seq)
    /\ maj = Len(seq)
    /\ UNCHANGED << seq, i, candidate, count, maj >>

(*---------------------------------------------------------------------*)
(*  Next-state relation                                                *)
(*---------------------------------------------------------------------*)
Next ==
    \/ AlgoStep
    \/ CountMajStep
    \/ Done

(*---------------------------------------------------------------------*)
(*  Specification                                                     *)
(*---------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<seq, i, candidate, count, maj>>

(*---------------------------------------------------------------------*)
(*  Safety property: Type correctness (no type errors)                *)
(*---------------------------------------------------------------------*)
TypeOK ==
    /\ seq \in Seq(Value)
    /\ i \in Nat
    /\ candidate \in Value
    /\ count \in Nat
    /\ maj \in Nat

(*---------------------------------------------------------------------*)
(*  Helper predicate: candidate is the only possible majority value  *)
(*---------------------------------------------------------------------*)
CandidateIsOnlyPossibleMajority ==
    /\ Count(seq, candidate) > Len(seq) / 2
    /\ \A v \in Value :
          (Count(seq, v) > Len(seq) / 2) => v = candidate

(*---------------------------------------------------------------------*)
(*  Stronger invariant: the candidate is the only possible majority   *)
(*---------------------------------------------------------------------*)
Inv == CandidateIsOnlyPossibleMajority

(*---------------------------------------------------------------------*)
(*  Correctness invariant (mirrors the description)                   *)
(*---------------------------------------------------------------------*)
Correct ==
    /\ i = Len(seq)
    /\ maj = Count(seq, candidate)
    /\ (\A v \in Value :
          (Count(seq, v) > Len(seq) / 2) => v = candidate)

=============================================================================