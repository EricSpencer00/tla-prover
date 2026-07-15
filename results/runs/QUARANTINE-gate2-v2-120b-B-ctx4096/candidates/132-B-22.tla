------------------------- MODULE MCMajority ----------------------------------
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS A, B, C, bound

(* Ensure that the constant 'bound' is a natural number (including 0). *)
ASSUME bound \in Nat

Value == {A, B, C}

(* The set of all sequences (including the empty sequence) over Value
   whose length does not exceed the constant 'bound'. *)
BoundedSeq(S) == { s \in Seq(S) : Len(s) <= bound }

VARIABLES seq, i, cand, cnt

(* The 'Majority' module (assumed to be in the same directory) defines the
   algorithm. It expects the constants and variables defined here. *)
INSTANCE Majority

Init ==
    /\ seq = << >>
    /\ i   = 1
    /\ cand = {}
    /\ cnt  = 0

Next ==
    \/ /\ i <= bound
       /\ /\ \E v \in Value :
              /\ cnt = 0 => cand' = v
              /\ cnt > 0  => cand' = cand
           /\ cnt' = IF cnt = 0 THEN 1 ELSE IF v = cand THEN cnt + 1 ELSE cnt - 1
           /\ seq' = Append(seq, v)
           /\ i'   = i + 1
    \/ /\ i > bound
       /\ UNCHANGED << seq, i, cand, cnt >>

Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

=============================================================================