------------------------- MODULE MC_SumSequence -------------------------
(***************************************************************************)
(* Bounded TLC model for SumSequence.  The proof module keeps the genuine   *)
(* unbounded Seq operator; this wrapper supplies only the finite model      *)
(* override used by TLC.                                                   *)
(***************************************************************************)
EXTENDS SumSequence
CONSTANT bound
ASSUME bound \in Nat

LimitedSeq(S) == UNION { [1 .. k -> (S \cap Values)] : k \in 0 .. bound }
=============================================================================
