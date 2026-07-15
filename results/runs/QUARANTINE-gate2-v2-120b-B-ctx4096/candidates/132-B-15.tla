---- MODULE MCMajority ------------------------------------
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS A, B, C, bound

(* The constant 'bound' is the maximum length of the sequences we consider.
   The original specification mistakenly required 'bound' to be **not** a natural
   number, which makes the model impossible to instantiate.  The intended
   meaning is that 'bound' *is* a natural number, i.e., a non‑negative integer. *)
ASSUME bound \in Nat

(* The set of possible values that can appear in a sequence. *)
Value == {A, B, C}

(* All sequences (functions from 1..n to Value) whose length n is between
   0 and 'bound', inclusive. *)
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

(* Initial state: an empty sequence, and the algorithm's internal variables
   (candidate and count) are set to arbitrary but well‑typed values. *)
Init ==
    /\ seq = ""
    /\ i = 0
    /\ cand \in Value
    /\ cnt \in Nat

(* One step of the Boyer‑Moore majority‑vote algorithm. *)
Next ==
    \/ /\ i < bound
       /\ i' = i + 1
       /\ seq' = seq \o <<Value[i']>>
       /\ IF i' = 1
          THEN /\ cand' = Value[i']
               /\ cnt' = 1
          ELSE IF cnt = 0
               THEN /\ cand' = Value[i']
                    /\ cnt' = 1
               ELSE IF cand = Value[i']
                    THEN /\ cand' = cand
                         /\ cnt' = cnt + 1
                    ELSE /\ cand' = cand
                         /\ cnt' = cnt - 1
    \/ /\ i = bound
       /\ UNCHANGED <<seq, cand, cnt, i>>

(* Specification of the system's behavior. *)
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

(* Invariant stating that the candidate is always one of the allowed values. *)
CandInv == cand \in Value

=============================================================================