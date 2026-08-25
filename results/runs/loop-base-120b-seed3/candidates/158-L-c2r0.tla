---- MODULE Voting ----
EXTENDS Integers, FiniteSets, TLC

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(*--- Model‑checking bounds ---*)
MCAcceptor == {a1, a2, a3}
MCValue    == {v1, v2}
MCQuorum   == { {a1, a2}, {a2, a3}, {a1, a3} }
MCBallot   == -1 .. 2

(*--- Convenience aliases ---*)
AcceptorSet == MCAcceptor
ValueSet    == MCValue
QuorumSet   == MCQuorum
BallotSet   == MCBallot

VARIABLES votes, thresh

(*--- Initial state ---*)
Init ==
    /\ votes = [a \in AcceptorSet |-> {}]
    /\ thresh = [a \in AcceptorSet |-> -1]

(*--- Safety of a vote ---*)
Safe(b, v) ==
    \A c \in BallotSet :
        (c < b) =>
            \E q \in QuorumSet :
                \A a \in q :
                    ( [ballot |-> c, value |-> v] \in votes[a] )
                    \/ (thresh[a] > c)

(*--- Actions ---*)
PromiseIncrease(a, b) ==
    /\ a \in AcceptorSet
    /\ b \in BallotSet
    /\ b > thresh[a]
    /\ UNCHANGED votes
    /\ thresh' = [thresh EXCEPT ![a] = b]

Vote(a, b, v) ==
    /\ a \in AcceptorSet
    /\ b \in BallotSet
    /\ v \in ValueSet
    /\ b >= thresh[a]
    /\ \A vv \in votes[a] : vv.ballot # b
    /\ \A a2 \in AcceptorSet :
          \A vv \in votes[a2] :
              (vv.ballot = b) => (vv.value = v)
    /\ Safe(b, v)
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b, value |-> v] }]
    /\ thresh' = [thresh EXCEPT ![a] = b]

Next ==
    \/ \E a \in AcceptorSet, b \in BallotSet : PromiseIncrease(a, b)
    \/ \E a \in AcceptorSet, b \in BallotSet, v \in ValueSet : Vote(a, b, v)

(*--- Specification ---*)
Spec == Init /\ [][Next]_<<votes, thresh>>

(*--- Invariant ---*)
Inv ==
    /\ \A a \in AcceptorSet :
          \A vote \in votes[a] : Safe(vote.ballot, vote.value)
    /\ \A b \in BallotSet :
          \A a1, a2 \in AcceptorSet :
          \A v1, v2 \in ValueSet :
              ( [ballot |-> b, value |-> v1] \in votes[a1]
                /\ [ballot |-> b, value |-> v2] \in votes[a2] )
                => v1 = v2

(*--- Consistency property ---*)
ChosenVals ==
    { v \in ValueSet :
        \E b \in BallotSet, q \in QuorumSet :
            \A a \in q : [ballot |-> b, value |-> v] \in votes[a] }

ConsensusSpecBar == Cardinality(ChosenVals) <= 1

(*--- Symmetry set (permutations of acceptors) ---*)
MCSymmetry ==
    { f \in [AcceptorSet -> AcceptorSet] :
          \A a1, a2 \in AcceptorSet : f[a1] = f[a2] => a1 = a2 }

====