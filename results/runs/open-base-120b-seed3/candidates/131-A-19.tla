---- MODULE MajorityProof ----
CONSTANT Value

INSTANCE Majority WITH Value <- Value

Spec == Majority!Spec
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv == Majority!Inv
====