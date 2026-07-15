---- MODULE MCMajority ----------------------------------------------
EXTENDS Integers

CONSTANTS A, B, C, bound

(* bound should be a natural number (including zero) *)
ASSUME bound \in Nat

Value == {A, B, C}

(* A bounded sequence over a set S of length at most |bound| *)
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

(***************************************************************************)
(* The Majority module (assumed to be provided) defines the following:    *)
(*   - Init: the initial state                                            *)
(*   - Next: the state transition relation                                *)
(*   - Majority: the invariant stating that the returned candidate is a  *)
(*               majority element of the sequence, if one exists.        *)
(* For this self‑contained file we re‑declare the necessary operators in  *)
(* a minimal way that matches the intended semantics.                     *)
(***************************************************************************)

Init ==
    /\ seq = {}
    /\ i   = 0
    /\ cand = {}
    /\ cnt = 0

Next ==
    \/ /\ i < bound
       /\ i' = i + 1
       /\ seq' = seq \cup { i + 1 |-> CHOOSE v \in Value : TRUE }
       /\ IF cnt = 0
          THEN /\ cand' = seq'[i + 1]
               /\ cnt' = 1
          ELSE IF seq'[i + 1] = cand
               THEN /\ cand' = cand
                    /\ cnt' = cnt + 1
               ELSE /\ cand' = cand
                    /\ cnt' = cnt - 1
    \/ /\ i >= bound
       /\ UNCHANGED << seq, i, cand, cnt >>

(* Majority invariant: if there is an element that occurs more than half
   the length of the sequence, then cand equals that element. *)
Majority ==
    LET n == Len(seq) IN
    IF \E v \in Value : Cardinality({ j \in 1..n : seq[j] = v }) > n / 2
       THEN \A v \in Value :
               (Cardinality({ j \in 1..n : seq[j] = v }) > n / 2) => cand = v
       ELSE TRUE

=============================================================================