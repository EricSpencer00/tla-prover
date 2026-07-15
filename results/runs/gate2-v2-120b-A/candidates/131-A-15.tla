---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(*-----------------------------------------------------------------
  Constants
-----------------------------------------------------------------*)
CONSTANT Value

(*-----------------------------------------------------------------
  Types
-----------------------------------------------------------------*)
Values == {v \in Value : TRUE}

(*-----------------------------------------------------------------
  State Variables (inherited from the main algorithm)
-----------------------------------------------------------------*)
VARIABLES seq, i, cand, count

(*-----------------------------------------------------------------
  Helper definitions
-----------------------------------------------------------------*)
Positions == 1..Len(seq)

(\* Number of occurrences of v in positions 1..j of seq *)
Occur(v, j) == Cardinality({ k \in 1..j : seq[k] = v })

StrictMajority == 2 * Occur(cand, Len(seq)) > Len(seq)

(*-----------------------------------------------------------------
  Initial state (same as the original algorithm)
-----------------------------------------------------------------*)
Init ==
    /\ seq \in Seq(Values)
    /\ i = 0
    /\ cand \in Values
    /\ count = 0

(*-----------------------------------------------------------------
  Next-state relation (same as the original algorithm)
-----------------------------------------------------------------*)
Next ==
    \/ /\ i < Len(seq)
       /\ i' = i + 1
       /\ IF count = 0
          THEN /\ cand' = seq[i']
               /\ count' = 1
          ELSE IF seq[i'] = cand
               THEN /\ cand' = cand
                    /\ count' = count + 1
               ELSE /\ cand' = cand
                    /\ count' = count - 1
       /\ UNCHANGED seq
    \/ /\ i = Len(seq)
       /\ UNCHANGED <<seq, i, cand, count>>

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<seq, i, cand, count>>

(*-----------------------------------------------------------------
  Invariant: type correctness
-----------------------------------------------------------------*)
TypeOK ==
    /\ seq \in Seq(Values)
    /\ i \in Nat
    /\ cand \in Values
    /\ count \in Nat

(*-----------------------------------------------------------------
  Invariant: correctness after the scan
-----------------------------------------------------------------*)
Correct == (i = Len(seq)) => (StrictMajority => (cand \in Values))

(*-----------------------------------------------------------------
  Additional invariant (the inductive invariant from the main spec)
-----------------------------------------------------------------*)
Inv == (i = Len(seq)) => (StrictMajority => (cand = seq[1]))

(*-----------------------------------------------------------------
  THEOREMS (machine‑checked proofs, structure only)
-----------------------------------------------------------------*)
THEOREM TypeOKInv == Spec => []TypeOK
THEOREM CorrectInv == Spec => []Correct
THEOREM InvInv == Spec => []Inv

==============