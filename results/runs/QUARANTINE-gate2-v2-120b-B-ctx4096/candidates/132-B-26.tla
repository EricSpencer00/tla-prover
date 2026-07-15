---- MODULE MCMajority -------------------------------------------
EXTENDS Integers, Sequences

CONSTANTS A, B, C, bound

(* Ensure that bound is a non‑negative natural number. *)
ASSUME bound \in Nat

Value == {A, B, C}

(* BoundedSeq(S) is the set of all finite sequences over S whose length
   does not exceed the constant bound. *)
BoundedSeq(S) == { s \in Seq(S) : Len(s) \le bound }

VARIABLES seq, i, cand, cnt

(* The initial state: an empty sequence, index i = 1, no candidate, and
   a zero count. *)
Init == 
    /\ seq = <<>>
    /\ i = 1
    /\ cand = {}
    /\ cnt = 0

(* Deterministically choose the next element of the sequence from the
   three possible values. *)
Next == 
    \/ /\ i <= bound
       /\ \E v \in Value :
            /\ seq' = Append(seq, v)
            /\ i'   = i + 1
            /\ cand' = cand
            /\ cnt'  = cnt
    \/ /\ i > bound
       /\ UNCHANGED <<seq, i, cand, cnt>>

(* A convenient definition of the set of all possible states. *)
vars == <<seq, i, cand, cnt>>

(* The safety invariant that must hold in every reachable state. *)
Safe == 
    /\ i \in 1 .. bound + 1
    /\ Len(seq) = i - 1
    /\ seq \in BoundedSeq(Value)
    /\ (cnt = 0) \/ (cand \in Value /\ cnt \in Nat)

(* The specification is the standard Init /\ [][Next]_vars. *)
Spec == Init /\ [][Next]_vars

====