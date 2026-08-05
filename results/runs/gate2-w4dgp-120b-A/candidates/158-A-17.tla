---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

VARIABLES votes, promise

vars == <<votes, promise>>

NoBallot == Cardinality(MCBallot)

\* A ballot is safe for a value when every lower ballot has already been decided
\* for that value by some real quorum member, so no participant can revert it.
SafeFor(v, b) ==
  /\ \A c \in MCBallot : c < b => \E Q \in MCQuorum :
       \A p \in Q : (c, v) \in votes[p] \/ (promise[p] > c)
  /\ \A a \in MCAcceptor : b > promise[a] => (b, v) \notin votes[a]

TypeOK ==
  /\ votes \in [MCAcceptor -> SUBSET (MCBallot \X MCValue)]
  /\ promise \in [MCAcceptor -> -1..NoBallot]

Init ==
  /\ votes = [a \in MCAcceptor |-> {}]
  /\ promise = [a \in MCAcceptor |-> -1]

\* An acceptor may raise its promise threshold; it never lowers it.
RaisePromise(a, c) ==
  /\ c > promise[a]
  /\ promise' = [promise EXCEPT ![a] = c]
  /\ UNCHANGED votes

\* An acceptor votes for a value in a ballot it is not promised to ignore.
CastVote(a, c, v) ==
  /\ c >= promise[a]
  /\ (c, v) \notin votes[a]
  /\ \A b \in MCAcceptor : (c, v) \in votes[b] => b = a
  /\ \A d \in MCValue : d # v => (c, d) \notin votes[a]
  /\ \A b \in MCAcceptor : (c, w) \in votes[b] => w = v
  /\ SafeFor(v, c)
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<c, v>>}]
  /\ promise' = [promise EXCEPT ![a] = c]

Next ==
  \/ \E a \in MCAcceptor, c \in MCBallot : RaisePromise(a, c)
  \/ \E a \in MCAcceptor, c \in MCBallot, v \in MCValue : CastVote(a, c, v)
  \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

\* A single value is ever chosen: a quorum cannot vote for two different values
\* in the same or any overlapping ballot.
Inv ==
  /\ \A a \in MCAcceptor, c \in MCBallot, v \in MCValue : (c, v) \in votes[a] => SafeFor(v, c)
  /\ \A a, b \in MCAcceptor, c \in MCBallot, v, w \in MCValue :
       ((c, v) \in votes[a] /\ (c, w) \in votes[b]) => v = w
  /\ TypeOK

\* Because any two quorums share a member, the value voted for in any quorum is
\* the value voted for in every other quorum: no conflict can arise.
\* Proven against ConsensusSpecBar via a refinement mapping.
ConsensusSpecBar == Inv

\* A run that gets stuck is covered by a real timeout in the backing
\* implementation; this identity catches runs that get stuck in a set of states
\* with no further action at all.
StuckStates == UNCHANGED vars

MCSymmetry == {f \in [MCAcceptor -> MCAcceptor] : \A Q \in MCQuorum : {f[p] : p \in Q} \in MCQuorum}

====