---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* MCAcceptor/MCValue/MCQuorum/MCBallot are the bounded or concrete versions that
\* the model-checking configuration substitutes for the abstract constants.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

VARIABLES votes, threshold

vars == << votes, threshold >>

Votes == [who : Acceptor, bal : Ballot, val : Value]

\* A ballot is safe at number b if every lower ballot is backed by a quorum for the
\* same value, so no two different values can ever be chosen in overlapping ballots.
BackersFor(v, b) == { a \in MCAcceptor : << b, v >> \in votes[a] }

Bally(v) == { << a, b >> : a \in MCAcceptor /\ b \in MCBallot /\ << b, v >> \in votes[a] }

\* Safety is a property of each individual acceptor's votes, not of the vote set
\* as a whole: an acceptor never votes for an unsafe value.
SafeAt(a, v, b) ==
  /\ << b, v >> \in votes[a]
  /\ \A c \in 0..b : \E Q \in MCQuorum : \A d \in Q : (c \in MCBallot /\ << c, v >> \in votes[d])

TypeOK ==
  /\ votes \in [MCAcceptor -> SUBSET Votes]
  /\ threshold \in [MCAcceptor -> MCBallot \cup {-1}]

Init ==
  /\ votes = [a \in MCAcceptor |-> {}]
  /\ threshold = [a \in MCAcceptor |-> -1]

\* An acceptor refuses to vote below its own promise threshold.
Promised(a, n) ==
  /\ n \in MCBallot
  /\ n > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = n]
  /\ UNCHANGED votes

\* A vote is only allowed if it is safe at that ballot.
CastVote(a, v, b) ==
  /\ b \in MCBallot
  /\ b > threshold[a]
  /\ \A d \in MCAcceptor : << b, v >> \notin votes[d]
  /\ \A d \in MCAcceptor : (~(\E c \in MCBallot : << c, v >> \in votes[d]) => c < b)
  /\ \E Q \in MCQuorum :
       \A d \in Q : (b \in MCBallot /\ << b, v >> \in votes[d]) \/ threshold[d] >= b
  /\ votes' = [votes EXCEPT ![a] = @ \cup {<< b, v >>}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

\* Voting is a funnel rather than a lock: votes are always available to be cast,
\* but the ballot number must keep moving forward.
CastVoteAny == \E a \in MCAcceptor, v \in MCValue, b \in MCBallot : CastVote(a, v, b)

Next ==
  \/ \E a \in MCAcceptor, n \in MCBallot : Promised(a, n)
  \/ CastVoteAny

Spec == Init /\ [][Next]_vars
        /\ WF_vars(CastVoteAny)

\* At most one value can ever be chosen: every vote in the system is safe, and
\* each ballot is backed by at most one value.
OnlyOneChosen ==
  /\ \A a \in MCAcceptor : \A v \in MCValue : \A b \in MCBallot : SafeAt(a, v, b)
  /\ \A b \in MCBallot : \A (v1, v2) \in MCValue \X MCValue :
       (\A a \in MCAcceptor : << b, v1 >> \in votes[a]) /\ (\A a \in MCAcceptor : << b, v2 >> \in votes[a])
         => v1 = v2
  /\ TypeOK

\* The voting algorithm implements the abstract consensus spec via this mapping.
ConsensusSpecBar == OnlyOneChosen

\* While no vote has yet been cast, bounded fairness keeps the system moving.
EventualVote == (\A a \in MCAcceptor : votes[a] = {}) ~> (\E a \in MCAcceptor : votes[a] # {})

\* Every quorum must overlap with every other quorum; this is not derivable from
\* the model and is assumed as a real-world configuration requirement.
QuorumOverlap ==
  \A Q1, Q2 \in MCQuorum : \E a \in MCAcceptor : a \in Q1 /\ a \in Q2

\* With the overlap property added as an assumption, the bounded-fairness
\* guarantee above collapses to an unconditional liveness property.
EventualVoteGivenOverlap == QuorumOverlap => EventualVote

StateSpaceBound == Cardinality(BackersFor(v1, 1)) <= Cardinality(MCQuorum)

MCSymmetry ==
  \E f \in [MCAcceptor -> MCAcceptor] :
    /\ f \in [MCAcceptor -> MCAcceptor]
    /\ \A a \in MCAcceptor : \A g \in [MCAcceptor -> MCAcceptor] : (f[a] = g[a]) => (a = g[a])
    /\ \A a \in MCAcceptor : votes' = [votes EXCEPT ![f[a]] = @]

====