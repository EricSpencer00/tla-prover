-------------------------- MODULE MCMajority --------------------------
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS A, B, C, bound

(* The set of possible values. *)
Value == {A, B, C}

(* Sequences of values whose length is at most 'bound'. *)
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

(* Initialization: start with the empty sequence and default candidate/counter. *)
Init ==
    /\ seq = <<>>
    /\ i = 0
    /\ cand \in Value
    /\ cnt = 0

(* The core step of the majority vote algorithm. *)
Step ==
    \/ /\ i < bound
       /\ /\ i' = i + 1
          /\ seq' = Append(seq, Choose v \in Value: TRUE)
          /\ IF cnt = 0
                THEN /\ cand' = seq[i']
                     /\ cnt' = 1
                ELSE IF seq[i'] = cand
                        THEN /\ cand' = cand
                             /\ cnt' = cnt + 1
                        ELSE /\ cand' = cand
                             /\ cnt' = cnt - 1
    \/ /\ i = bound
       /\ UNCHANGED <<seq, i, cand, cnt>>

(* The full specification. *)
Spec == Init /\ [][Step]_<<seq, i, cand, cnt>>

=============================================================================