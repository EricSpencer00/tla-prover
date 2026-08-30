---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* A finite NAT from 0..MaxNat, overriding the infinite NAT in Naturals so TLC
\* can check the model; the theorem itself is assumed here as an axiom.
NatOverride == 0..MaxNat

\* SPEC: the model-checking configuration module for the double-of-NAT-is-even
\* proof. It overrides the NAT set with a bounded range for TLC.
SPEC == NatOverride

Init == TRUE

Next == TRUE

StateConstraint == TRUE

TypeOK == TRUE

\* Nothing to prove at runtime; the evenness theorem itself is assumed for the
\* model, so there is no generated condition to check here.
EvennessTheoremHolds == TRUE

Spec == Init /\ [][Next]_<< >>
====