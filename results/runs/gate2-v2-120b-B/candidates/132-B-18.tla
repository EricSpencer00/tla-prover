---- MODULE MCMajority ----
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)
EXTENDS Integers

CONSTANTS A, B, C, bound
(* The bound must be a natural number (including zero). *)
ASSUME bound \in Nat

Value == {A, B, C}
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

(* Initial state: empty sequence, index 0, no candidate, zero count. *)
Init ==
    /\ seq = [j \in 1..bound |-> A]  \* dummy initialization; will be overridden by InitSeq below
    /\ i = 0
    /\ cand = A
    /\ cnt = 0

(* Generate a concrete sequence over Value of length at most bound. *)
InitSeq ==
    \E n \in 0..bound:
        \E s \in [1..n -> Value]:
            /\ seq = s
            /\ i = 0
            /\ cand = A
            /\ cnt = 0

(* Next-step action implementing the Boyer‑Moore majority‑vote algorithm. *)
Next ==
    \/ /\ i < Len(seq)
       /\ LET v == seq[i + 1] IN
          /\ IF cnt = 0 THEN
                 /\ cand' = v
                 /\ cnt' = 1
             ELSE
                 /\ IF cand = v THEN
                        /\ cnt' = cnt + 1
                    ELSE
                        /\ cnt' = cnt - 1
           /\ i' = i + 1
           /\ UNCHANGED <<seq>>

    \/ /\ i = Len(seq)
       /\ UNCHANGED <<seq, i, cand, cnt>>

(* Derived operator for the length of a (possibly empty) sequence. *)
Len(s) == 
    IF DOMAIN s = {} THEN 0
    ELSE Max(DOMAIN s)

vars == <<seq, i, cand, cnt>>

Spec == Init \/ InitSeq \/ [][Next]_vars

====