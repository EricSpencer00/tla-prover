---- MODULE Voting ----
EXTENDS Naturals

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

AcceptorSet == Acceptor
ValueSet == Value
QuorumSet == Quorum
BallotSet == Ballot

VARIABLES votes, thr
vars == <<votes, thr>>

VotePairs == [ac : AcceptorSet, b : BallotSet, v : ValueSet]
VoteFor(a, b, v) == [ac |-> a, b |-> b, v |-> v]

TypeOK ==
  /\ votes \subseteq VotePairs
  /\ thr \in [AcceptorSet -> (BallotSet \cup {-1})]

Init ==
  /\ votes = {}
  /\ thr = [a \in AcceptorSet |-> -1]

SafeAt(v, b) ==
  \A c \in BallotSet :
    c < b => \E q \in QuorumSet :
      \A a \in q :
        \/ VoteFor(a, c, v) \in votes
        \/ \A av \in votes : av.ac = a => av.b < c

BallotPromised(a, b) ==
  /\ thr[a] < b
  /\ thr' = [thr EXCEPT ![a] = b]
  /\ UNCHANGED votes

Vote(a, b, v) ==
  /\ b >= thr[a]
  /\ ~(\E av \in votes : av.ac = a /\ av.b = b)
  /\ \A av \in votes : av.b = b => av.v = v
  /\ SafeAt(v, b)
  /\ votes' = votes \cup {VoteFor(a, b, v)}
  /\ thr' = [thr EXCEPT ![a] = b]

Next == \E a \in AcceptorSet, b \in BallotSet, v \in ValueSet : BallotPromised(a, b) \/ Vote(a, b, v)

Spec == Init /\ [][Next]_vars

QuorumVoted(v, b) == \E q \in QuorumSet : \A a \in q : VoteFor(a, b, v) \in votes

Chosen == { v \in ValueSet : \E b \in BallotSet : QuorumVoted(v, b) }

Inv ==
  /\ \A av \in votes : SafeAt(av.v, av.b)
  /\ \A av \in votes, aw \in votes :
       (av.b = aw.b) => (av.v = aw.v)
  /\ TypeOK

ConsensusSpecBar == \A x \in Chosen, y \in Chosen : x = y

MCAcceptor == AcceptorSet
MCValue == ValueSet
MCQuorum == QuorumSet
MCBallot == BallotSet

MCSymmetry == {}
====