---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Value

(*--------------------------------------------------------------------
  State variables (inherited from the main majority‑vote specification)
--------------------------------------------------------------------*)
VARIABLES seq, i, candidate, count

(*--------------------------------------------------------------------
  Initialization (same as in the main specification)
--------------------------------------------------------------------*)
Init ==
  /\ seq \in Seq(Value)
  /\ i = 1
  /\ count = 0
  /\ candidate \in Value

(*--------------------------------------------------------------------
  Next‑state relation (the Boyer‑Moore update step)
--------------------------------------------------------------------*)
Next ==
  \/ /\ i <= Len(seq)
     /\ i' = i + 1
     /\ IF count = 0 THEN
           /\ candidate' = seq[i]
           /\ count' = 1
        ELSE IF candidate = seq[i] THEN
           /\ candidate' = candidate
           /\ count' = count + 1
        ELSE
           /\ candidate' = candidate
           /\ count' = count - 1
  \/ /\ i > Len(seq)
     /\ UNCHANGED <<seq, i, candidate, count>>

(*--------------------------------------------------------------------
  Tuple of all variables for the stuttering operator
--------------------------------------------------------------------*)
vars == <<seq, i, candidate, count>>

(*--------------------------------------------------------------------
  Specification
--------------------------------------------------------------------*)
Spec == Init /\ [][Next]_vars

(*--------------------------------------------------------------------
  Type correctness invariant
--------------------------------------------------------------------*)
TypeOK ==
  /\ seq \in Seq(Value)
  /\ i \in Nat
  /\ candidate \in Value
  /\ count \in Nat

(*--------------------------------------------------------------------
  Auxiliary invariant (can be used in proofs)
--------------------------------------------------------------------*)
Inv ==
  /\ i \in 1..(Len(seq) + 1)
  /\ (count = 0 => candidate \in Value)

(*--------------------------------------------------------------------
  Main correctness property: any strict‑majority element must equal the
  final candidate after the whole sequence has been processed.
--------------------------------------------------------------------*)
Correct ==
  /\ i = Len(seq) + 1
  /\ \A v \in Value :
        (Cardinality({j \in 1..Len(seq) : seq[j] = v}) > Len(seq) / 2) => v = candidate

====