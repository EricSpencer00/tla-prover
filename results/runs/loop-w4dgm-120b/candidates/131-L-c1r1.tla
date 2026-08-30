---- MODULE MajorityProof ----
EXTENDS Integers, Sequences, FiniteSets, MajorityVote

CONSTANTS Value

\* The module contains an interactive proof of the Boyer-Moore majority vote
\* algorithm's correctness. No new state or action is introduced beyond what
\* MajorityVote already defines; this module adds the proof obligations.

TypeOK == MajorityVote.TypeOK

\* After scanning the whole sequence, any value occurring in a strict majority
\* of positions must equal the candidate the algorithm has retained.
Correct == MajorityVote.Correct

Inv == MajorityVote.Inv

Spec == MajorityVote.Spec

====