---- MODULE MC_Synod ----
(* Hand-authored (prove-TLA): no upstream MC wrapper exists for Synod.tla's
   SynodSpec == \EE chosen, allInput : IS(chosen, allInput)!ISpec -- TLC
   cannot check a temporal-exists (\EE) directly. Synod's own IS(chosen,
   allInput) == INSTANCE Inner is a top-level (non-LOCAL) operator, so an
   external module can call it with concrete (non-hidden) VARIABLES instead
   of the existentially-quantified ones, exposing an ordinary checkable
   Init/Next. See corpus/configs/MC_WRAPPERS.md and PATCHES.md (spec 50) for
   the two Synod.tla defects this exposed and fixed in corpus/configs/patches/50.tla. *)
EXTENDS Synod

VARIABLES chosen, allInput

MCInit == IS(chosen, allInput)!IInit
MCNext == IS(chosen, allInput)!INext
MCSpec == IS(chosen, allInput)!ISpec

TypeOK ==
  /\ input \in [Proc -> Inputs]
  /\ output \in [Proc -> {NotAnInput} \cup Inputs]
  /\ chosen \in {NotAnInput} \cup Inputs
  /\ allInput \subseteq Inputs

====
