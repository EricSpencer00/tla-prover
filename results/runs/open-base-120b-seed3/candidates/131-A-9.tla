---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences
CONSTANT Value

(* Import the main majority‑vote specification. *)
INSTANCE Majority AS M

(* ---------------------------------------------------------------------- *)
(*  Type correctness invariant                                            *)
(* ---------------------------------------------------------------------- *)
TypeOK ==
  /\ M!cand \in Value \/ M!cand = "None"
  /\ M!count \in Nat
  /\ M!i \in Nat
  /\ M!seq \in Seq(Value)
  /\ M!n = Len(M!seq)

(* ---------------------------------------------------------------------- *)
(*  Helper definition: the (unique) majority element of a sequence, if any *)
(* ---------------------------------------------------------------------- *)
Majority(seq_) ==
  CHOOSE v \in Value :
    Cardinality({j \in 1..Len(seq_) : seq_[j] = v}) > Len(seq_) / 2

(* ---------------------------------------------------------------------- *)
(*  Correctness invariant: after the whole sequence is processed, the     *)
(*  candidate equals the majority element (when one exists).            *)
(* ---------------------------------------------------------------------- *)
Correct ==
  (M!i = M!n) => (M!cand = Majority(M!seq))

(* ---------------------------------------------------------------------- *)
(*  Combined invariant used in the proof                                   *)
(* ---------------------------------------------------------------------- *)
Inv == TypeOK /\ Correct

(* ---------------------------------------------------------------------- *)
(*  Specification of the algorithm (as defined in the main module)        *)
(* ---------------------------------------------------------------------- *)
Spec == M!Spec

====