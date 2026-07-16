------------------------------- MODULE MCMajority --------------------------------
(****************************************************************************)
(* TLA+ module for model checking the majority vote algorithm for all       *)
(* sequences over three elements of bounded length.                         *)
(****************************************************************************)

EXTENDS Integers, Sequences

CONSTANTS A, B, C, bound

(* ------------------------------------------------------------------------- *)
(* The bound must be a natural number (including zero).                     *)
(* ------------------------------------------------------------------------- *)
ASSUME bound \in Nat

Value == {A, B, C}

(* The set of all sequences over Value whose length is at most bound. *)
BoundedSeq(S) == { s \in Seq(S) : Len(s) \in 0..bound }

VARIABLES seq, i, cand, cnt

(* ------------------------------------------------------------------------- *)
(*  Definitions taken from the Majority module, inlined to avoid the import   *)
(*  of an external module.                                                    *)
(* ------------------------------------------------------------------------- *)

(* Candidate and count after processing the first j elements of a sequence. *)
Cand(j, s) ==
  IF j = 0 THEN ""                 \* no candidate before any element
  ELSE
    LET prevCand == Cand(j-1, s) IN
    LET prevCnt  == Cnt(j-1, s)  IN
    LET x == s[j]                IN
    IF prevCnt = 0 THEN x
    ELSE IF prevCand = x THEN x
    ELSE prevCand

Cnt(j, s) ==
  IF j = 0 THEN 0
  ELSE
    LET prevCand == Cand(j-1, s) IN
    LET prevCnt  == Cnt(j-1, s)  IN
    LET x == s[j]                IN
    IF prevCnt = 0 THEN 1
    ELSE IF prevCand = x THEN prevCnt + 1
    ELSE prevCnt - 1

(* ------------------------------------------------------------------------- *)
(* Initial state: any bounded sequence, with i = 0, and no candidate/count.   *)
(* ------------------------------------------------------------------------- *)

Init ==
  /\ seq \in BoundedSeq(Value)
  /\ i = 0
  /\ cnt = 0
  /\ cand = ""

(* ------------------------------------------------------------------------- *)
(* One step of the algorithm: advance i and update cand / cnt accordingly.   *)
(* ------------------------------------------------------------------------- *)

Next ==
  /\ i < Len(seq)
  /\ i' = i + 1
  /\ cand' = Cand(i', seq)
  /\ cnt'  = Cnt(i', seq)
  /\ UNCHANGED seq

(* ------------------------------------------------------------------------- *)
(* Fairness: eventually the loop finishes.                                    *)
(* ------------------------------------------------------------------------- *)

LoopDone == i = Len(seq)

Spec == Init /\ [][Next]_<<seq, i, cand, cnt>> /\ WF_<<seq, i, cand, cnt>>(Next)

=============================================================================