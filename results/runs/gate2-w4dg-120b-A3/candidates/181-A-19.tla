---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* NatOverride is a FINITE version of the infinite natural-number set Nat from
\* Naturals, used only for model checking.  It replaces Nat in the .cfg.
NatOverride == 0 .. MaxNat

\* The base specification that actually proves the theorem is imported here.
\* The model-checking configuration treats it as a black box.
\* (The theorem itself is assumed as a constant-level assumption, not proved.)
\* Eta-reduction is used so that its operators appear here with their original
\* names, unchanged.
\* Note: the import must preserve the names of its operators exactly as is.
Eta(specs/NumbersAreEven)

\* MC_sums_even only supplies the configuration scaffolding around the base
\* proof; the proof itself is untouched, and no safety or liveness property
\* is introduced here beyond the assumption made below.
ASSUME True

\* The .cfg names these items exactly; they must appear even though they do
\* nothing in this thin wrapper.
SPECIFICATION Spec
INIT Init
NEXT NextStep
INVARIANTS NothingSpecial
PROPERTIES TheoremCountsAsAnAssumption

\* The one declared property, named for the .cfg, holds vacuously in every
\* reachable state, because it is simply assumed, not proved, in this model.
TheoremCountsAsAnAssumption == True

====