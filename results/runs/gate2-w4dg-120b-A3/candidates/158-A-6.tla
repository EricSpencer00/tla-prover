---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

Acceptors == {a1, a2, a3}
Values == {v1, v2}
Quorums == {q1, q2, q3}
Ballots == {0, 1, 2}

\* Substitute operators for the constants; these are the finite-bounded versions
\* the .cfg file expects to use instead of the original constants.
MCAcceptor == Acceptors
MCValue == Values
MCQuorum == Quorums
MCBallot == Ballots

VARIABLES votes, threshold

vars == <<votes, threshold>>

VoteRec == [accepter: MCAcceptor, ballot: MCBallot, value: MCValue]

QuorumSafe(v, b) ==
  \A c \in MCBallot :
    ((c < b /\ c >= 0) => (\E Q \in MCQuorum : \A a \in Q : (<<a, c, v>> \in votes) \/ (threshold[a] >= c)))

TypeOK ==
  /\ votes \subseteq VoteRec
  /\ threshold \in [MCAcceptor -> MCBallot \cup {-1}]

Init ==
  /\ votes = {}
  /\ threshold = [a \in MCAcceptor |-> -1]

RaiseThreshold(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

Vote(a, b, v) ==
  /\ b >= threshold[a]
  /\ \A vv \in Values : <<a, b, vv>> \notin votes
  /\ QuorumSafe(v, b)
  /\ votes' = votes \cup {<<a, b, v>>}
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in MCAcceptor, b \in MCBallot : RaiseThreshold(a, b)
  \/ \E a \in MCAcceptor, b \in MCBallot, v \in Values : Vote(a, b, v)

Spec == Init /\ [][Next]_vars

VoterSafe == \A r \in votes : QuorumSafe(r.value, r.ballot)

BallotSingleton == \A a1 \in MCAcceptor, a2 \in MCAcceptor, b \in MCBallot :
  (\E v1 \in MCValue, v2 \in MCValue :
     (<<a1, b, v1>> \in votes /\ <<a2, b, v2>> \in votes) => v1 = v2)

Inv == TypeOK /\ VoterSafe /\ BallotSingleton

ChosenValues == {v \in MCValue : \E Q \in MCQuorum, b \in MCBallot : \A a \in Q : <<a, b, v>> \in votes}

ConsensusSpecBar == Cardinality(ChosenValues) =< 1

\* Symmetry: any permutation of the acceptors is indistinguishable to the spec.
MCSymmetry == {f \in [MCAcceptor -> MCAcceptor] :
  \A p, q \in MCAcceptor : (p = q <=> f[p] = f[q])}

====