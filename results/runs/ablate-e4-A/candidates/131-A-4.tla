---- MODULE MajorityProof ----
EXTENDS MajoritySpec, FiniteSets, TLC

CONSTANT Value

Spec == MajoritySpec.Spec

TypeOK == MajoritySpec.TypeOK

Correct == MajoritySpec.Correct

Inv == MajoritySpec.Inv

====