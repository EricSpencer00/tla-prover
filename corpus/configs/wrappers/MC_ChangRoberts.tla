---- MODULE MC_ChangRoberts ----
(* Hand-authored (no upstream/sibling wrapper found for ChangRoberts).
   Id must be a length-N sequence of distinct naturals (module's own ASSUME,
   Id \in Seq(Nat) /\ Len(Id) = N /\ injective) -- no .cfg tuple literal
   syntax, supplied as a zero-arity operator override, same technique as
   corpus/configs/wrappers/MC_HanoiSeq.tla. *)
EXTENDS ChangRoberts
IdConst == <<3, 1, 2>>
====
