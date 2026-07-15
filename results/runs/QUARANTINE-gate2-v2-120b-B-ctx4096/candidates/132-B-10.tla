---- MODULE MCMajority ----
EXTENDS Integers, Sequences, FiniteSets, Majority

CONSTANTS A, B, C, bound

(* The bound must be a natural number (0 or greater). *)
bound \in Nat

Value == {A, B, C}

(* All sequences over Value with length between 0 and bound inclusive. *)
BoundedSeq == { s \in [1..n -> Value] : n \in 0..bound }

VARIABLES seq, i, cand, cnt

(* Initial state: choose any bounded sequence, start index at 1,
   and initialize the Boyer‑Moore variables to the first element
   and count 1 (or 0/undef for the empty sequence). *)
Init ==
  /\ seq \in BoundedSeq
  /\ i = 1
  /\ IF Len(seq) = 0
        THEN /\ cand = {}
             /\ cnt  = 0
        ELSE /\ cand = seq[1]
             /\ cnt  = 1

(* One step of the Boyer‑Moore majority‑vote algorithm. *)
Step ==
  /\ i < Len(seq)
  /\ i' = i + 1
  /\ IF cnt = 0
        THEN /\ cand' = seq[i']
             /\ cnt'  = 1
        ELSE IF seq[i'] = cand
                THEN /\ cand' = cand
                     /\ cnt'  = cnt + 1
                ELSE /\ cand' = cand
                     /\ cnt'  = cnt - 1

(* When the sequence has been fully scanned, the algorithm stays
   in a terminal state that leaves all variables unchanged. *)
Done ==
  /\ i = Len(seq)
  /\ UNCHANGED <<seq, i, cand, cnt>>

Next == Step \/ Done

Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

=============================================================================