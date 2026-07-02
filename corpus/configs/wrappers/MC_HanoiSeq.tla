---- MODULE MC_HanoiSeq ----
(* Hand-authored (no upstream wrapper found for HanoiSeq in tla-examples;
   confirmed by direct search). A, B, C are sequence-valued CONSTANTS with no
   .cfg literal syntax; supplied here as zero-arity operator overrides, per
   the module's own worked example in its header comment
   (A == <<1,2,3>>; B == <<>>; C == <<>>). *)
EXTENDS HanoiSeq
AConst == <<1, 2, 3>>
BConst == <<>>
CConst == <<>>
====
