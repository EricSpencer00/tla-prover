---- MODULE MCMajority ---------------------------------------------------------
EXTENDS Integers, Sequences, FiniteSets, Majority

CONSTANTS A, B, C, bound

(* The original specification incorrectly assumed that `bound` is NOT a natural
   number, which caused the model checker to abort.  For a bounded sequence
   of length up to `bound` we need `bound` to be a natural number (including
   zero).  The corrected assumption therefore requires `bound` to be in Nat. *)
ASSUME bound \in Nat

(* The set of possible vote values. *)
Value == {A, B, C}

(* A bounded sequence over a set S is any sequence of length n where
   0 ≤ n ≤ bound.  This definition uses the built‑in datatype for sequences. *)
BoundedSeq(S) == { s \in [1..n -> S] : n \in 0..bound }

VARIABLES seq, i, cand, cnt

(* Initial state: empty sequence, index 0, no candidate, zero count. *)
Init ==
    /\ seq = <<>>
    /\ i = 0
    /\ cand = {}
    /\ cnt = 0

(* Advance to the next element in the sequence (if any). *)
Next ==
    \/ /\ i < bound
       /\ i' = i + 1
       /\ seq' = seq \o << Value[ i' ] >>
       /\ (* Update the Boyer–Moore majority candidate and count. *)
          IF cnt = 0 THEN
              /\ cand' = seq[i']
              /\ cnt' = 1
          ELSE IF seq[i'] = cand THEN
              /\ cnt' = cnt + 1
              /\ cand' = cand
          ELSE
              /\ cnt' = cnt - 1
              /\ cand' = cand
    \/ /\ i = bound
       /\ UNCHANGED << seq, cand, cnt >>

(* The overall specification. *)
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

=============================================================================