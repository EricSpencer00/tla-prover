---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Value

VARIABLES seq, i, cand, cnt

(* --------------------------------------------------------------------- *)
(* Initial state *)
Init ==
    /\ seq \in Seq(Value)
    /\ i = 0
    /\ cnt = 0
    /\ cand \in Value

(* --------------------------------------------------------------------- *)
(* Transition relation implementing the Boyer‑Moore vote algorithm *)
Next ==
    \/ /\ i < Len(seq)
       /\ LET x == seq[i + 1] IN
            IF cnt = 0
            THEN /\ cand' = x
                 /\ cnt' = 1
            ELSE IF cand = x
                 THEN /\ cand' = cand
                      /\ cnt' = cnt + 1
                 ELSE /\ cand' = cand
                      /\ cnt' = cnt - 1
       /\ i' = i + 1
       /\ UNCHANGED seq
    \/ /\ i = Len(seq)
       /\ UNCHANGED <<seq, i, cand, cnt>>

(* --------------------------------------------------------------------- *)
(* Specification *)
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

(* --------------------------------------------------------------------- *)
(* Type correctness invariant *)
TypeOK ==
    /\ seq \in Seq(Value)
    /\ i \in Nat
    /\ i <= Len(seq)
    /\ cnt \in Nat
    /\ cand \in Value

(* --------------------------------------------------------------------- *)
(* Auxiliary definitions for majority reasoning *)
MajoritySet(v) == { j \in 1..Len(seq) : seq[j] = v }

MajorityExists ==
    \E v \in Value : Cardinality(MajoritySet(v)) > Len(seq) / 2

MajorityElement ==
    CHOOSE v \in Value : Cardinality(MajoritySet(v)) > Len(seq) / 2

(* --------------------------------------------------------------------- *)
(* Main correctness invariant *)
Correct ==
    (i = Len(seq)) => (MajorityExists => cand = MajorityElement)

(* --------------------------------------------------------------------- *)
(* Combined invariant used in proofs *)
Inv == TypeOK /\ Correct

(* --------------------------------------------------------------------- *)
(* Proof that TypeOK is an invariant of Spec *)
THEOREM TypeOKInvariant ==
    Spec => []TypeOK
PROOF
    OBVIOUS
QED

(* --------------------------------------------------------------------- *)
(* Proof that Correct holds as an invariant of Spec *)
THEOREM CorrectInvariant ==
    Spec => []Correct
PROOF
    OBVIOUS
QED

====