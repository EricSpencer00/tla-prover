---- MODULE MCMajority ----
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, Naturals

CONSTANTS A, B, C, bound

(* The bound must be a natural number (0 or greater). *)
ASSUME bound \in Nat

(* The set of possible values in the sequence. *)
Value == {A, B, C}

(* Set of all sequences over Value whose length is at most bound. *)
BoundedSeq(S) == { s \in Seq(S) : Len(s) \in 0..bound }

VARIABLES seq, i, cand, cnt

(* Initialize the state. *)
Init ==
    /\ seq \in BoundedSeq(Value)
    /\ i = 0
    /\ cand = CHOOSE x \in Value : TRUE   \* any value from Value
    /\ cnt = 0

(* One step of the majority algorithm (Boyer‑Moore). *)
Next ==
    \/ /\ i < Len(seq)
       /\ i' = i + 1
       /\ IF cnt = 0
          THEN /\ cand' = seq[i']
               /\ cnt' = 1
          ELSE IF seq[i'] = cand
               THEN /\ cnt' = cnt + 1
                    /\ UNCHANGED cand
               ELSE /\ cnt' = cnt - 1
                    /\ UNCHANGED cand
       /\ UNCHANGED << >>
    \/ /\ i = Len(seq)
       /\ UNCHANGED << seq, i, cand, cnt >>

(* The full behavior of the system. *)
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

=============================================================================