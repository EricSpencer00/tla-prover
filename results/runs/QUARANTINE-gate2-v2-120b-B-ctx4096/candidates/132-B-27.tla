---- MODULE MCMajority ---------------------------------------------- 
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS A, B, C, bound

(* The set of possible values *)
Value == {A, B, C}

(* Sequences of values whose length does not exceed the bound. *)
BoundedSeq == { s \in Seq(Value) : Len(s) <= bound }

VARIABLES seq, i, cand, cnt

(* Initial state: empty sequence, index 0, arbitrary candidate and zero count. *)
Init ==
    /\ seq = <<>>
    /\ i   = 0
    /\ cand \in Value
    /\ cnt = 0

(* One step of the Moore majority vote algorithm. *)
Step ==
    \/ /\ i < bound
       /\ \E v \in Value :
            /\ seq' = Append(seq, v)
            /\ i'   = i + 1
            /\ IF cnt = 0 THEN cand' = v ELSE cand' = cand
            /\ IF cnt = 0 THEN cnt' = 1 ELSE 
               IF v = cand THEN cnt' = cnt + 1 ELSE cnt' = cnt - 1
       \/ /\ i = bound
          /\ UNCHANGED << seq, i, cand, cnt >>

(* Specification *)
Spec == Init /\ [][Step]_<<seq, i, cand, cnt>>

(* Safety property: after the bound steps, the candidate is a majority element
   if one exists. *)
MajorityExists ==
    /\ i = bound
    /\ \E x \in Value : Cardinality({ j \in 1..bound : seq[j] = x }) > bound / 2

Safe == MajorityExists => cand \in Value /\ 
        Cardinality({ j \in 1..bound : seq[j] = cand }) > bound / 2

=============================================================================