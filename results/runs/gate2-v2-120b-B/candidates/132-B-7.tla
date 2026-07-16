-------------------------- MODULE MCMajority --------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS A, B, C, bound

(* The constant 'bound' must be a natural number (including zero). *)
ASSUME bound \in Nat

Value == {A, B, C}

(* Bounded sequences over a set S, of length up to 'bound'. *)
BoundedSeq(S) == UNION { [1..n -> S] : n \in 0..bound }

VARIABLES seq, i, cand, cnt

(* Instantiate the generic Majority module with the concrete set of values. *)
INSTANCE Majority \* No arguments needed; it uses the constant 'Value'.

(* Initial state: empty sequence, index 1, no candidate, count 0. *)
Init ==
    /\ seq = <<>>
    /\ i = 1
    /\ cand = NULL
    /\ cnt = 0

(* Extend the sequence by one element from Value, if length < bound. *)
Extend ==
    /\ i <= bound
    /\ \E v \in Value :
          /\ seq' = Append(seq, v)
          /\ i'   = i + 1
          /\ cand' = IF cnt = 0 THEN v ELSE cand
          /\ cnt'  = IF cnt = 0 THEN 1
                    ELSE IF v = cand THEN cnt + 1
                    ELSE cnt - 1

(* The next-state relation. *)
Next ==
    \/ Extend
    \/ UNCHANGED <<seq, i, cand, cnt>>

(* Complete specification. *)
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

=============================================================================