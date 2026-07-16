------------------------- MODULE MCMajority ----------------------------------
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS A, B, C, bound

(* Ensure that bound is a natural number (including zero) *)
ASSUME bound \in Nat

Value == {A, B, C}

(* BoundedSeq(S) is the set of all sequences over S whose length is at most bound *)
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

(* The algorithm from Majority module is used unchanged *)
INSTANCE Majority

(* Initial state: start with empty sequence, iterator i = 1, and no candidate *)
Init ==
    /\ seq = <<>>
    /\ i = 1
    /\ cand = Null
    /\ cnt = 0

(* An arbitrary element from Value is appended to the sequence, respecting the bound *)
SeqAppend ==
    /\ i <= bound
    /\ \E v \in Value :
        /\ seq' = Append(seq, v)
        /\ i' = i + 1
        /\ UNCHANGED <<cand, cnt>>

(* The Majority algorithm step, invoked only when there are elements left to process *)
MajorityStep ==
    /\ i <= Len(seq)
    /\ MajorityStep(i, seq, cand, cnt, cand', cnt')
    /\ i' = i + 1
    /\ UNCHANGED seq

Next ==
    \/ SeqAppend
    \/ MajorityStep

(* The overall specification: start in Init and repeatedly apply Next *)
Spec ==
    Init /\ [][Next]_<<seq, i, cand, cnt>>

=============================================================================