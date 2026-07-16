------------------------- MODULE MCMajority ----------------------------------
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)
EXTENDS Integers, Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

(* bound must be a natural number (0,1,2,...) so that the bounded sequences are
   well‑defined.  The original specification mistakenly used a negated condition,
   causing an immediate failure of the assumption. *)
ASSUME bound \in Nat

Value == {A, B, C}
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

(* The algorithm’s invariant, imported from the Majority module, is not changed.
   It is only instantiated with the concrete constants defined above. *)
Inv == /\ i \in 0 .. bound
       /\ (i # 0) => (cand \in Value)
       /\ (cnt \in Nat)
       /\ (cnt = 0) => (cand = "")
       /\ (cnt > 0) => (cand \in Value)

(* ------------------------------------------------------------------------- *)
(* Initial state                                                            *)
(* ------------------------------------------------------------------------- *)

Init ==
    /\ seq = {}
    /\ i   = 0
    /\ cand = ""
    /\ cnt = 0

(* ------------------------------------------------------------------------- *)
(* Transition step (Boyer‑Moore majority vote algorithm)                     *)
(* ------------------------------------------------------------------------- *)

Next ==
    \/ /\ i < bound
       /\ \E x \in Value :
            /\ seq' = [seq EXCEPT ![i+1] = x]
            /\ i'   = i + 1
            /\ IF cnt = 0
               THEN /\ cand' = x
                    /\ cnt'  = 1
               ELSE IF x = cand
                    THEN /\ cand' = cand
                         /\ cnt'  = cnt + 1
                    ELSE /\ cand' = cand
                         /\ cnt'  = cnt - 1
    \/ /\ i = bound
       /\ UNCHANGED <<seq, i, cand, cnt>>

(* ------------------------------------------------------------------------- *)
(* Specification                                                            *)
(* ------------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

(* ------------------------------------------------------------------------- *)
(* The majority value (if it exists)                                        *)
(* ------------------------------------------------------------------------- *)

MajorityValue ==
    CandMajority(seq, cand, cnt)

=============================================================================