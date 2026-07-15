---- MODULE MCMajority ----
EXTENDS MajorityVote, Sequences, TLC

CONSTANTS A, B, C, bound, Seq

(* The set of possible element values *)
Values == {A, B, C}

(* All sequences over Values of length at most bound *)
Seq == { s \in Seq1 : Len(s) <= bound /\ \A i \in 1..Len(s) : s[i] \in Values }

VARIABLES seq, pos, cand, cnt

Init == MajorityVote.Init
Next == MajorityVote.Next

Spec == Init /\ [][Next]_<<seq, pos, cand, cnt>>

TypeOK == MajorityVote.TypeOK
Correct == MajorityVote.Correct
Inv == MajorityVote.Inv

====