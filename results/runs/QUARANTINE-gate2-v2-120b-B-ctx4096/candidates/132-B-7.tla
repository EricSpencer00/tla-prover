---- MODULE MCMajority -------------------------------------------------
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, Naturals

CONSTANTS A, B, C, bound

(* The set of possible vote values. *)
Value == {A, B, C}

(* The set of all sequences (including the empty one) over Value whose
   length does not exceed the constant bound. *)
BoundedSeq(S) == { s \in Seq(S) : Len(s) \in 0..bound }

VARIABLES seq, i, cand, cnt

(* The majority-vote algorithm is imported from the Majority module.          *)
INSTANCE Majority

(* ------------------------------------------------------------------------- *)
(* Initial predicate: the sequence is chosen nondeterministically from       *)
(* BoundedSeq(Value), and the other variables are set to their initial       *)
(* values as required by the Majority algorithm.                             *)
(* ------------------------------------------------------------------------- *)
Init ==
    /\ seq \in BoundedSeq(Value)
    /\ i   = 1
    /\ cand = {}
    /\ cnt  = 0

(* ------------------------------------------------------------------------- *)
(* Next-state relation: either we are still scanning the sequence, or we    *)
(* have finished (in which case the state is stuttering).                    *)
(* ------------------------------------------------------------------------- *)
Next ==
    \/ /\ i <= Len(seq)
       /\ i' = i + 1
       /\ /\
          IF cnt = 0 THEN
              /\ cand' = { seq[i] }
              /\ cnt'  = 1
          ELSE
              /\ cand' = cand
              /\ IF seq[i] \in cand THEN cnt' = cnt + 1
                 ELSE cnt' = cnt - 1
       /\ UNCHANGED << seq >>
    \/ /\ i > Len(seq)
       /\ UNCHANGED << seq, i, cand, cnt >>

Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

=============================================================================