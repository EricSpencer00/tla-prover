---- MODULE MajorityProof ----
EXTENDS TLC, MajorityVote

CONSTANT Value

Init == MajorityVote.Init
Next == MajorityVote.Next
Spec == MajorityVote.Spec

TypeOK == MajorityVote.TypeOK
Correct == MajorityVote.Correct
Inv == MajorityVote.Inv

====