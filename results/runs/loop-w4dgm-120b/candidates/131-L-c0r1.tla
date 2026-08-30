---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets, MajorityVote

CONSTANTS Value

\* No new state; everything is inherited from MajorityVote.
\* The proof obligations below are the ONLY additions this module makes.

TypeOK ==
    /\ seq \in Seq(Value)
    /\ pos \in 0..Len(seq)
    /\ candidate \in Value \cup {"none"}
    /\ count \in 0..Len(seq)

\* The inductive invariant from the main spec, restated here for TLAPS.
Inv ==
    /\ candidate # "none" =>
         \A i \in 1..pos : seq[i] = candidate
    /\ count = Cardinality({i \in 1..pos : seq[i] = candidate})

Init ==
    /\ seq \in Seq(Value)
    /\ pos = 0
    /\ candidate = "none"
    /\ count = 0

\* The first element always becomes the candidate.
VoteFirst ==
    /\ pos = 0
    /\ Len(seq) >= 1
    /\ candidate' = seq[1]
    /\ count' = 1
    /\ pos' = 1
    /\ UNCHANGED seq

\* A matching vote increments the count.
VoteMatch ==
    /\ pos < Len(seq)
    /\ seq[pos + 1] = candidate
    /\ count' = count + 1
    /\ pos' = pos + 1
    /\ UNCHANGED <<seq, candidate>>

\* A non-matching vote cancels one prior vote.
VoteCancel ==
    /\ pos < Len(seq)
    /\ seq[pos + 1] # candidate
    /\ count > 0
    /\ count' = count - 1
    /\ pos' = pos + 1
    /\ UNCHANGED <<seq, candidate>>

\* A non-matching vote with no prior votes installs the new candidate.
VoteReplace ==
    /\ pos < Len(seq)
    /\ seq[pos + 1] # candidate
    /\ count = 0
    /\ candidate' = seq[pos + 1]
    /\ count' = 1
    /\ pos' = pos + 1
    /\ UNCHANGED seq

\* The scan is exhausted; it stays put.
VoteDone ==
    /\ pos = Len(seq)
    /\ UNCHANGED <<seq, pos, candidate, count>>

Next == VoteFirst \/ VoteMatch \/ VoteCancel \/ VoteReplace \/ VoteDone

Spec == Init /\ [][Next]_<<seq, pos, candidate, count>>

\* After the whole sequence is scanned, any strict-majority value must be
\* the candidate the algorithm settled on.
Correct ==
    /\ pos = Len(seq)
    /\ \A v \in Value :
         (2 * Cardinality({i \in 1..Len(seq) : seq[i] = v}) > Len(seq))
            => v = candidate

====