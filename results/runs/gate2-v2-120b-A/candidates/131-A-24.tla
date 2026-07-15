---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, TLC

(*--------------------------------------------------------------------*)
(*  Constants *)
CONSTANT Value

(*--------------------------------------------------------------------*)
(*  State variables (inherited from the main Boyer-Moore spec) *)
VARIABLES candidate, count, i, seq, n

(*--------------------------------------------------------------------*)
(*  Helper definitions *)

(*  Positions before index i (1..n) *)
Positions(i) == { j \in 1..n : j < i }

(*  Number of occurrences of a value v in positions before i *)
FreqBefore(v, i) == Cardinality({ j \in Positions(i) : seq[j] = v })

(*  Type predicate *)
CandidateRange == IF n = 0 THEN {} ELSE { seq[j] : j \in 1..n }
TypeOK ==
  /\ seq \in [1..n -> Value]
  /\ candidate \in CandidateRange
  /\ count \in Nat

(*--------------------------------------------------------------------*)
(*  Initial state *)

Init ==
  /\ i = 1
  /\ candidate = "None"               \* placeholder, not in Value, used only before first element
  /\ count = 0
  /\ (* seq and n are nondeterministically chosen consistent with the constant set Value *)
     \E m \in Nat :
        /\ n = m
        /\ n >= 0
        /\ seq \in [1..n -> Value]

(*--------------------------------------------------------------------*)
(*  Transition (next-state relation) *)

Next ==
  \/ \/ /\ i > n
        /\ UNCHANGED <<candidate, count, i, seq, n>>
     \/ /\ i <= n
        /\ LET v == seq[i] IN
           IF count = 0 THEN
              /\ candidate' = v
              /\ count' = 1
              /\ i' = i + 1
              /\ UNCHANGED <<seq, n>>
           ELSE IF candidate = v THEN
              /\ count' = count + 1
              /\ i' = i + 1
              /\ UNCHANGED <<candidate, seq, n>>
           ELSE
              /\ count' = count - 1
              /\ i' = i + 1
              /\ UNCHANGED <<candidate, seq, n>>

(*--------------------------------------------------------------------*)
(*  Specification *)

Spec == Init /\ [][Next]_<<candidate, count, i, seq, n>>

(*--------------------------------------------------------------------*)
(*  Invariants *)

(*  Type correctness invariant, already defined above as TypeOK *)
Inv == TypeOK

(*  Correctness invariant: any strict majority value must equal the candidate *)
StrictMajority(v) ==
  /\ v \in Value
  /\ 2 * Cardinality({ j \in 1..n : seq[j] = v }) > n

Correct ==
  /\ i > n
  /\ \A v \in Value :
        StrictMajority(v) => v = candidate

(*--------------------------------------------------------------------*)
(*  Theorems (to be proved by TLAPS) *)

THEOREM TypeOKIsInvariant == Spec => []TypeOK
THEOREM CorrectIsInvariant == Spec => []Correct

(*--------------------------------------------------------------------*)
(*  End of module *)
====