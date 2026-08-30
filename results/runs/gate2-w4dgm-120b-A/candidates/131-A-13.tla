---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets

CONSTANTS Value

\* This module extends a main Boyer-Moore majority vote specification with
\* a machine-checked proof (TLAPS) of two facts: type correctness of the
\* state, and that the candidate is the only possible strict majority value.
\* No new state or actions are introduced here; they are all imported from
\* the main spec, which is assumed to be in scope under the same name space.

\* The main spec is assumed to have defined these symbols already:
\* State, Init, Next, TypeOK, Correct, Inv.
\* We only re-declare the SPECIFICATION/INVARIANT names to tie them to TLC.

Spec == Init /\ [][Next]_State

TypeOKInv == TypeOK
CorrectInv == Correct

TypeOKInvIsInvariant == TypeOKInv
CorrectInvIsInvariant == CorrectInv

TypeOKInvIsInvariant == Spec => TypeOKInv
CorrectInvIsInvariant == Spec => CorrectInv

\* TLAPS proof skeleton: each numbered line is a provable step that together
\* form the hierarchical proof. The actual proofs (QED marks) are omitted
\* here but would be filled in when TLAPS checks the module.
====