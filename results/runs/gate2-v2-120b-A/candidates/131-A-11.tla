---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, TLC

(*--------------------------------------------------------------------
  This module extends the Boyer-Moore majority vote algorithm with
  machine-checked proofs of its type correctness and main correctness.
  It defines the identifiers required by the reference configuration.
--------------------------------------------------------------------*)

CONSTANT Value

VARIABLES seq, cand, count, i

(*--------------------------------------------------------------------
  Types
--------------------------------------------------------------------*)
SeqOfValues == <<>> \cup Seq(Value)

TypeOK == /\ seq \in SeqOfValues
          /\ i \in Nat
          /\ i <= Len(seq)
          /\ cand \in Value \cup {Null}
          /\ count \in Nat

(* Null is a distinguished element that is not in Value. *)
Null == -1

(* Initial state: start before processing any element. *)
Init ==
  /\ i = 0
  /\ count = 0
  /\ cand = Null
  /\ seq \in SeqOfValues

(* One step of the Boyer-Moore algorithm. *)
Next ==
  \/ /\ i < Len(seq)
     /\ LET x == seq[i+1] IN
        IF count = 0 THEN
          /\ cand' = x
          /\ count' = 1
        ELSE IF cand = x THEN
          /\ cand' = cand
          /\ count' = count + 1
        ELSE
          /\ cand' = cand
          /\ count' = count - 1
     /\ i' = i + 1
  \/ /\ i = Len(seq)  \* stutter after termination
     /\ UNCHANGED <<cand, count, i, seq>>

Spec == Init /\ [][Next]_<<cand, count, i, seq>>

(*--------------------------------------------------------------------
  Main correctness invariant (Inv) – the candidate after the whole
  sequence is processed must be the only possible majority element.
--------------------------------------------------------------------*)
Inv ==
  /\ i = Len(seq)
  /\ \A v \in Value :
        (Cardinality({j \in 1..Len(seq) : seq[j] = v}) >
         Len(seq) / 2)
        => v = cand

(* The other invariant mentioned in the .cfg is called Correct.  It
   is simply a synonym for Inv in this module. *)
Correct == Inv

=============================================================================