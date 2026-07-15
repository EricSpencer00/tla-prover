---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* Constants (instantiated in the .cfg)
\* ----------------------------------------------------------------------
CONSTANT a1          \* a distinguished acceptor (used only as an example)
CONSTANT Acceptor    \* the set of all acceptors
CONSTANT Value       \* the set of all values that may be chosen
CONSTANT Quorum      \* a set of quorums; each element is a subset of Acceptor
CONSTANT Ballot      \* the set of ballot numbers (natural numbers)

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
AcceptorSet == Acceptor
ValueSet    == Value
QuorumSet   == Quorum
BallotSet   == Ballot

\* ----------------------------------------------------------------------
\* Types for readability
\* ----------------------------------------------------------------------
Vote == [b : BallotSet, v : ValueSet]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES votes, threshold

\* votes[a] is the set of votes cast by acceptor a
\* threshold[a] is the minimal ballot number a will accept (initially -1)
\* ----------------------------------------------------------------------
vars == << votes, threshold >>

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ votes = [a \in AcceptorSet |-> {}]
  /\ threshold = [a \in AcceptorSet |-> -1]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* An acceptor a has not voted in ballot b
NoVoteInBallot(a, b) == \A v \in ValueSet : ~(<<b, v>> \in votes[a])

\* No acceptor votes for a different value in ballot b
UniqueValuePerBallot(b) ==
  \A a1, a2 \in AcceptorSet :
    \A v1, v2 \in ValueSet :
      (<<b, v1>> \in votes[a1] /\ <<b, v2>> \in votes[a2]) => v1 = v2

\* A quorum is a subset of acceptors
IsQuorum(q) == q \in QuorumSet /\ q \subseteq AcceptorSet

\* Overlap property (assumed to hold for all configured quorums)
QuorumsOverlap ==
  \A q1, q2 \in QuorumSet : q1 \cap q2 # {}

\* Quorum safety: a quorum q demonstrates that value v is safe at ballot b
QuorumSafeAt(q, b, v) ==
  IsQuorum(q) /\
  \A c \in BallotSet :
    c < b =>
      \E a \in q :
        (<<c, v>> \in votes[a]) \/ (threshold[a] > c)

\* A value v is safe at ballot b (exists a quorum proving safety)
SafeAt(b, v) ==
  \E q \in QuorumSet : QuorumSafeAt(q, b, v)

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. An acceptor raises its promise threshold without voting
RaisePromise ==
  \E a \in AcceptorSet :
    /\ \E newThresh \in BallotSet :
         newThresh > threshold[a]
    /\ threshold' = [threshold EXCEPT ![a] = newThresh]
    /\ UNCHANGED votes

\* 2. An acceptor casts a vote for value v in ballot b
VoteAction ==
  \E a \in AcceptorSet :
    /\ \E b \in BallotSet :
         /\ b >= threshold[a]
         /\ NoVoteInBallot(a, b)
         /\ \E v \in ValueSet :
              /\ SafeAt(b, v)
              /\ UniqueValuePerBallot(b)
              /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
              /\ threshold' = [threshold EXCEPT ![a] = b]

Next == \/ RaisePromise
        \/ VoteAction

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Safety invariant (captures the three invariants from the description)
\* ----------------------------------------------------------------------
Inv ==
  /\ \A a \in AcceptorSet :
        \A vote \in votes[a] :
          /\ vote \in Vote
          /\ SafeAt(vote.b, vote.v)
  /\ \A b \in BallotSet :
        \E v \in ValueSet :
          \A a \in AcceptorSet : <<b, v>> \in votes[a]
        \/ \A a \in AcceptorSet : NoVoteInBallot(a, b)  \* at most one value per ballot
  /\ QuorumsOverlap

\* ----------------------------------------------------------------------
\* Consensus property (derived from the safety invariant)
\* ----------------------------------------------------------------------
ConsensusSpecBar ==
  \A b1, b2 \in BallotSet :
    \A v1, v2 \in ValueSet :
      (\A a \in AcceptorSet : <<b1, v1>> \in votes[a]) /\
      (\A a \in AcceptorSet : <<b2, v2>> \in votes[a]) => v1 = v2

====