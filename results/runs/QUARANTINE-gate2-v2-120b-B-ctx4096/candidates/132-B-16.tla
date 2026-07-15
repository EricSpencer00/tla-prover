---- MODULE MCMajority ----
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)
EXTENDS Integers, Sequences

CONSTANTS bound

(* The bound must be a natural number (i.e., a non‑negative integer). *)
ASSUME bound \in Nat

Value == {"A", "B", "C"}

(* Sequences of elements taken from Value, whose length does not exceed bound. *)
BoundedSeq == { s \in Seq(Value) : Len(s) <= bound }

VARIABLES seq, i, cand, cnt

(*---------------------------------------------------------------------------
  Helper definitions
 ---------------------------------------------------------------------------*)
Init ==
    /\ seq = {}
    /\ i   = 1
    /\ cand = 0
    /\ cnt = 0

Next ==
    \/ /\ i <= bound
       /\ seq' = Append(seq, Value[i])
       /\ i'   = i + 1
       /\ cand' = cand
       /\ cnt'  = cnt

    \/ /\ i > bound
       /\ UNCHANGED << seq, i, cand, cnt >>

(*---------------------------------------------------------------------------
  Specification
 ---------------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

(*---------------------------------------------------------------------------
  Safety invariant: the current candidate and its count are always within
  the allowed domain and the count never becomes negative.
 ---------------------------------------------------------------------------*)
Inv ==
    /\ cand \in Value \/ cand = 0
    /\ cnt \in Nat
    /\ cnt <= Len(seq)

=============================================================================