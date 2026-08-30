---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets, MajorityVote

CONSTANTS Value

Spec == MajoritySpec

Init == MajorityInit

Next == MajorityNext

TypeOK == MajorityTypeOK

Correct == MajorityCorrect

Inv == MajorityInv

====