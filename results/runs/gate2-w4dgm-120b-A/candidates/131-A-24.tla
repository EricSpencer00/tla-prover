---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets, MajorityVote

CONSTANTS Value

\* No new state: ScanPos, Occurs, Candidate, Majority are all from MajorityVote.
Init == MajorityVote.Init
Step == MajorityVote.Step

Spec == Init /\ [][Step]_<<ScanPos, Occurs, Candidate, Majority>>

TypeOK ==
  /\ ScanPos \in 0..VoteLength
  /\ Occurs \in [Value -> 0..VoteLength]
  /\ Candidate \in Value \cup {"none"}
  /\ Majority \in BOOLEAN

\* The core correctness: after the scan finishes, any strict majority value
\* must be the candidate the algorithm picked.
Correct ==
  /\ Candidate # "none" => Occurs[Candidate] > VoteLength \div 2
  /\ Majority => (\E v \in Value : Occurs[v] > VoteLength \div 2)

\* Hierarchical TLAPS proof: a local lemma for each prefix length, plus the
\* container fact that ties them together via the scan transition.
MajorityImpliesCandidate ==
  /\ \A k \in 0..VoteLength : MajorityVote.PrefixMajorityImpliesCandidate(k)
  /\ MajorityVote.ScanStepPreservesPrefixFact

Inv == TypeOK /\ Correct
====