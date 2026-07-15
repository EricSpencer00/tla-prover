---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (instantiated in the .cfg)
\*   Acceptor : set of acceptor identifiers
\*   Value    : set of possible values
\*   Quorum   : set of quorums, each quorum is a subset of Acceptor
\*   Ballot   : set of ballot numbers (natural numbers)
\* ----------------------------------------------------------------------
CONSTANTS Acceptor, Value, Quorum, Ballot

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
AcceptorSet == Acceptor
ValueSet    == Value
QuorumSet   == Quorum
BallotSet   == Ballot

\* ----------------------------------------------------------------------
\* Type definitions
\* ----------------------------------------------------------------------
Vote == [ballot : BallotSet, val : ValueSet]

\* ----------------------------------------------------------------------
\* Variables
\*   votes[a]      : the set of votes that acceptor a has cast
\*   promise[a]    : the current promise threshold of acceptor a
\* ----------------------------------------------------------------------
VARIABLES votes, promise

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Votes cast by any acceptor
AllVotes == { v \in Vote : \E a \in AcceptorSet : v \in votes[a] }

\* The set of values that have been chosen (i.e., a quorum voted for them)
ChosenVals ==
  { v.val :
      \E b \in BallotSet :
        \E q \in QuorumSet :
          \A a \in q : [ballot |-> b, val |-> v.val] \in votes[a] }

\* Safety of a value at a given ballot
SafeAt(val, b) ==
  \A c \in BallotSet :
    (c < b) =>
      \E q \in QuorumSet :
        \A a \in q :
          ( [ballot |-> c, val |-> val] \in votes[a] )
          \/ (promise[a] > c)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ votes = [a \in AcceptorSet |-> {}]
  /\ promise = [a \in AcceptorSet |-> -1]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Increase promise threshold without voting
IncreasePromise ==
  \E a \in AcceptorSet :
    \E newB \in BallotSet :
      /\ newB > promise[a]
      /\ promise' = [promise EXCEPT ![a] = newB]
      /\ UNCHANGED votes

\* 2. Cast a vote for a value in a ballot
CastVote ==
  \E a \in AcceptorSet :
    \E b \in BallotSet :
      \E v \in ValueSet :
        /\ b >= promise[a]
        /\ \A w \in votes[a] : w.ballot # b          \* not already voted in this ballot
        /\ \A a2 \in AcceptorSet :
              \A w \in votes[a2] :
                (w.ballot = b) => (w.val = v)       \* no other value in same ballot
        /\ SafeAt(v, b)                               \* value is safe at b
        /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b, val |-> v] }]
        /\ promise' = [promise EXCEPT ![a] = b]
        /\ UNCHANGED << >>

\* Stuttering step to avoid deadlock when no action is enabled
Stutter == UNCHANGED << votes, promise >>

Next == IncreasePromise \/ CastVote \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<votes, promise>>

\* ----------------------------------------------------------------------
\* Invariant (required identifier: Inv)
\* It asserts that every vote in the system is safe at its ballot.
\* ----------------------------------------------------------------------
Inv == \A a \in AcceptorSet : \A v \in votes[a] : SafeAt(v.val, v.ballot)

\* ----------------------------------------------------------------------
\* Property: ConsensusSpecBar (the safety property described)
\* At most one value can ever be chosen.
\* ----------------------------------------------------------------------
ConsensusSpecBar == Cardinality(ChosenVals) <= 1

\* ----------------------------------------------------------------------
\* THEOREM (optional, not required by the cfg but useful for TLC)
\* ----------------------------------------------------------------------
THEOREM Spec => []Inv

=============================================================================