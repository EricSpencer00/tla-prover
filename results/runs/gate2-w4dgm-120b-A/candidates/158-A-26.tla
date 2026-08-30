---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

VoteRec == [ball : Ballot, val : Value]
BallotBound == 2
AcceptorSet == {a1, a2, a3}
ValueSet == {v1, v2}

VARIABLES votes, promised

vars == <<votes, promised>>

TypeOK ==
    /\ votes \in [Acceptor -> SUBSET VoteRec]
    /\ promised \in [Acceptor -> Ballot \cup {-1}]

Init ==
    /\ votes = [a \in AcceptorSet |-> {}]
    /\ promised = [a \in AcceptorSet |-> -1]

MakePromise(a, b) ==
    /\ b > promised[a]
    /\ promised' = [promised EXCEPT ![a] = b]
    /\ UNCHANGED votes

QuorumVoters(q, v, b) ==
    {a \in q : \E r \in votes[a] : r.ball = b /\ r.val = v}

HasQuorum(v, b) ==
    \E q \in Quorum : Cardinality(QuorumVoters(q, v, b)) = Cardinality(q)

Safe(v, b) ==
    /\ HasQuorum(v, b)
    /\ \A c \in 0..(b - 1) : \E q \in Quorum :
        /\ Cardinality({a \in q :
              \E r \in votes[a] : r.ball = c /\ r.val = v}) = Cardinality(q)
        /\ \A a \in q : \A r \in votes[a] : r.ball = c => r.val = v

CastVote(a, v, b) ==
    /\ b >= promised[a]
    /\ \A r \in votes[a] : r.ball # b
    /\ \A x \in AcceptorSet : \A r \in votes[x] : r.ball = b => r.val = v
    /\ Safe(v, b)
    /\ votes' = [votes EXCEPT ![a] = @ \cup {[ball |-> b, val |-> v]}]
    /\ promised' = [promised EXCEPT ![a] = b]

Next ==
    \/ \E a \in AcceptorSet, b \in 0..BallotBound : MakePromise(a, b)
    \/ \E a \in AcceptorSet, v \in ValueSet, b \in 0..BallotBound : CastVote(a, v, b)

Spec == Init /\ [][Next]_vars

ChosenValue ==
    {v \in ValueSet :
        \E q \in Quorum : \A a \in q : \E r \in votes[a] : r.val = v}

Inv ==
    /\ \A a \in AcceptorSet : \A r \in votes[a] : Safe(r.val, r.ball)
    /\ \A a, x \in AcceptorSet : \A r \in votes[a], s \in votes[x] :
           r.ball = s.ball => r.val = s.val
    /\ \A a \in AcceptorSet : promised[a] \in Ballot \cup {-1}

ConsensusSpecBar == ChosenValue \subseteq Value

MCSymmetry == {f \in [Acceptor -> Acceptor] :
    /\ \A a \in Acceptor : f[a] \in Acceptor
    /\ \A a, b \in Acceptor : (f[a] = f[b]) => (a = b)}

MCAcceptor == AcceptorSet
MCValue == ValueSet
MCQuorum == Quorum
MCBallot == 0..BallotBound

====