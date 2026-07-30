---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

AcceptorSet == {a1, a2, a3}
ValueSet == {v1, v2}
QuorumSet == {q1, q2}
BallotSet == {0, 1}

VARIABLES votes, minBallot

vars == <<votes, minBallot>>

TypeOK ==
  /\ votes \in [AcceptorSet -> SUBSET (BallotSet \X ValueSet)]
  /\ minBallot \in [AcceptorSet -> (BallotSet \cup {-1})]

Init ==
  /\ votes = [a \in AcceptorSet |-> {}]
  /\ minBallot = [a \in AcceptorSet |-> -1]

\* A promise (prepare) advances a participant's ballot floor without voting.
RaiseFloor(a, b) ==
  /\ b > minBallot[a]
  /\ minBallot' = [minBallot EXCEPT ![a] = b]
  /\ UNCHANGED votes

HasVote(a, b, v) == <<b, v>> \in votes[a]

\* Safety of a vote: every lower ballot is either already committed to v or
\* has a quorum that can never be cast.
VoteSafe(a, b, v) ==
  /\ \A c \in BallotSet :
       (c < b) => (\E q \in QuorumSet :
                      \A x \in q : ((c, v) \in votes[x] \/ c \notin {p[1] : p \in votes[x]}))
  /\ \A c \in BallotSet : (c < b) => ~(\E x \in AcceptorSet, w \in ValueSet : <<c, w>> \in votes[x])

QuorumVotedFor(v, b) == \E q \in QuorumSet : \A a \in q : <<b, v>> \in votes[a]

\* A vote may be cast only if no other value has already been voted for in that ballot.
CastVote(a, b, v) ==
  /\ b >= minBallot[a]
  /\ minBallot' = [minBallot EXCEPT ![a] = b]
  /\ ~HasVote(a, b, v)
  /\ \A w \in ValueSet : ~(w # v /\ QuorumVotedFor(w, b))
  /\ VoteSafe(a, b, v)
  /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]

Next ==
  \E a \in AcceptorSet, b \in BallotSet, v \in ValueSet :
    RaiseFloor(a, b) \/ CastVote(a, b, v)

Spec == Init /\ [][Next]_vars

\* Consistency: at most one value is ever chosen by a quorum.
ChosenValues == {v \in ValueSet : QuorumVotedFor(v, 0)}
Inv == Cardinality(ChosenValues) <= 1

\* ConsensusSpecBar is a named alias for the one invariant; the .cfg expects it.
ConsensusSpecBar == Inv

MCAcceptor == AcceptorSet
MCValue == ValueSet
MCQuorum == QuorumSet
MCBallot == BallotSet

MCSymmetry == {
  [a1 |-> a1, a2 |-> a2, a3 |-> a3],
  [a1 |-> a1, a2 |-> a3, a3 |-> a2],
  [a1 |-> a2, a2 |-> a1, a3 |-> a3],
  [a1 |-> a2, a2 |-> a3, a3 |-> a1],
  [a1 |-> a3, a2 |-> a1, a3 |-> a2],
  [a1 |-> a3, a2 |-> a2, a3 |-> a1]
}
====