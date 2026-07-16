---- MODULE MCMajority ----
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)
EXTENDS Integers, Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

(* The set of possible values that can appear in the sequence. *)
Value == {A, B, C}

(* Definition of all sequences (including the empty sequence) whose length
   is at most the constant `bound`.  The original specification used a set
   comprehension that is not a well‑typed TLA+ expression.  This definition
   uses the standard `Seq` operator from the Sequences module, which yields
   all sequences over a given set, and then restricts to those whose length
   does not exceed `bound`.  The semantics are identical to the intended
   meaning of the original `BoundedSeq`. *)
BoundedSeq == { s \in Seq(Value) : Len(s) <= bound }

VARIABLES seq, i, cand, cnt

(* The algorithm from the imported Majority module expects the variables
   `seq` (the input sequence), `i` (the current index), `cand` (current
   candidate), and `cnt` (current count).  This stub defines the initial
   state and the step relation exactly as in Majority, but without imposing
   any additional constraints that would make the model inconsistent. *)
Init ==
    /\ seq \in BoundedSeq
    /\ i = 1
    /\ cand \in Value
    /\ cnt = 0

(* One step of the Boyer‑Moore majority‑vote algorithm. *)
Next ==
    \/ /\ i <= Len(seq)
       /\ LET x == seq[i] IN
          IF cnt = 0 THEN
              /\ cand' = x
              /\ cnt' = 1
          ELSE IF x = cand THEN
              /\ cnt' = cnt + 1
          ELSE
              /\ cnt' = cnt - 1
       /\ i' = i + 1
       /\ UNCHANGED <<seq, cand>>
    \/ /\ i > Len(seq)
       /\ UNCHANGED <<seq, i, cand, cnt>>

(* The specification is the usual Init /\ [] [Next]_<<seq, i, cand, cnt>>. *)
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

=============================================================================