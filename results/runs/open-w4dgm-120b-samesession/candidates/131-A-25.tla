---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets, MajorityMain

CONSTANTS Value

Spec == MajoritySpec

Init == MajorityInit

Next == MajorityNext

TypeOK == MajorityTypeOK

Correct == MajorityCorrect

Inv == MajorityInvariant

====