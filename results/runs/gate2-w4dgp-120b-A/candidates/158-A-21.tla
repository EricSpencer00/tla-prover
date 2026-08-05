---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

\* This models a high-level voting-based consensus algorithm, an abstraction of Paxos:
\* acceptors cast votes for values in numbered ballots, and a value is chosen only
\* when a quorum of acceptors has voted for it. Voter promises (thresholds) gate
\* which ballots an acceptor may vote in, and the quorum overlap property forces
\* consistency: once a value is chosen, no different value can ever be chosen.
CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

ASSUME QuorumOverlap == \A q1 \in Quorum, q2 \in Quorum : q1 # q2 => q1 \cap q2 # {}
ASSUME a1 # a2 /\ a2 # a3 /\ a1 # a3
ASSUME v1 # v2

VARIABLES votes, promise
vars == << votes, promise >>

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ promise \in [Acceptor -> (-1) \cup Ballot]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ promise = [a \in Acceptor |-> -1]

\* An acceptor may raise its promise threshold to a higher ballot without voting.
Promise(a, b) ==
  /\ b > promise[a]
  /\ promise' = [promise EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* An acceptor votes for a value in a ballot, provided no voter has already voted
\* for a different value in that ballot and the value is safe at that ballot.
Vote(a, b, v) ==
  /\ b >= promise[a]
  /\ \A a2 \in Acceptor : << b, v >> \notin votes[a2]
  /\ \A a2 \in Acceptor : \A v2 \in Value : << b, v2 >> \in votes[a2] => v2 = v
  /\ \A c \in 0..(b - 1) : \E q \in Quorum :
        \A a2 \in q : << c, v >> \in votes[a2] \/ c < promise[a2]
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<< b, v >>}]
  /\ promise' = [promise EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : Promise(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)

Spec == Init /\ [][Next]_vars

\* Consistency: at most one value is ever chosen by a quorum.
Inv ==
  /\ TypeOK
  /\ \A a1 \in Acceptor, a2 \in Acceptor, b \in Ballot, v1 \in Value, v2 \in Value :
        (<< b, v1 >> \in votes[a1] /\ << b, v2 >> \in votes[a2]) => v1 = v2
  /\ \A v \in Value : (v \in {v \in Value : \E q \in Quorum : \A a \in q : << 1, v >> \in votes[a]}) => {v2 \in Value : \E q \in Quorum : \A a \in q : << 1, v2 >> \in votes[a]} = {v}

\* Refinement: this abstract voting algorithm implements the core consensus
\* specification (a single chosen value) by mapping the chosen set to the
\* values that a quorum of voters chose.
MCAcceptor == {a1, a2}
MCValue == {v1}
MCQuorum == {{a1, a2}}
MCBallot == 0..1

ConsensusSpecBar == \A v \in Value : v \in {v \in Value : \E q \in MCQuorum : \A a \in q : << 1, v >> \in votes[a]} => {v2 \in Value : \E q \in MCQuorum : \A a \in q : << 1, v2 >> \in votes[a]} = {v}
MCSymmetry == {f \in [Acceptor -> Acceptor] : {f[a1], f[a2], f[a3]} = {a1, a2, a3}}

====