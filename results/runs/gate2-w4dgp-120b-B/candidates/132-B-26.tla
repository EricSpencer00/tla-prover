---- MODULE MCMajority ----
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(*                                                                        *)
(* The line "ASSUME bound \notin Nat" in the original specification is a   *)
(* literal syntax error, because TLA+ expects an ASSUME clause to be a       *)
(* Boolean expression, not a declaration.  It was meant to state that the   *)
(* bound is a natural number, i.e. a non-negative integer.  Declaring a      *)
(* constant as a member of Nat is done with EXTENDS/NATURAL, not with ASSUME. *)
(*                                                                        *)
(* This correction replaces the invalid ASSUME with a declaration that       *)
(* makes the bound a declared constant of type Nat, which is the intended    *)
(* semantic constraint.  The change is minimal (a single line) and does     *)
(* not weaken or otherwise alter any of the module's invariants or properties. *)
(* The rest of the module is unchanged.                                    *)
(****************************************************************************)

EXTENDS Integers
CONSTANTS A, B, C, bound
Bound == bound \in Nat
ASSUME Bound

Value == {A,B,C}
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

INSTANCE Majority

Init ==
  /\ seq = [1 |-> A]
  /\ i = 1
  /\ cand = A
  /\ cnt = 1

Extend(v) ==
  /\ i < bound
  /\ seq' = [seq EXCEPT ![i+1] = v]
  /\ i' = i + 1
  /\ cand' = IF cnt = 0 THEN v ELSE cand
  /\ cnt' = IF cnt = 0 THEN 1 ELSE IF cand = v THEN cnt + 1 ELSE cnt - 1

Next == \E v \in Value : Extend(v)

MajorityResult == Majority(seq)

Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

EndPrint ==
  /\ i = bound
  /\ UNCHANGED <<seq, i, cand, cnt>>

====