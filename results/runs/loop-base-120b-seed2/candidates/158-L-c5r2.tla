---- MODULE Voting ----
EXTENDS Integers, FiniteSets, TLC

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

VARIABLES votes, promise

Vote == [ballot : Ballot, value : Value]

Init ==
    /\ votes   = [a \in Acceptor |-> {}]
    /\ promise = [a \in Acceptor |-> -1]

Safe(v, b) ==
    \A c \in 0..(b - 1) :
        \E Q \in Quorum :
            \A a \in Q :
                ( \E vt \in votes[a] : vt.ballot = c /\ vt.value = v )
                \/ promise[a] > c

IncreasePromise ==
    \E a \in Acceptor :
        \E nb \in Ballot :
            /\ nb > promise[a]
            /\ promise' = [promise EXCEPT ![a] = nb]
            /\ votes'   = votes

CastVote ==
    \E a \in Acceptor :
        \E v \in Value :
            \E b \in Ballot :
                /\ b >= promise[a]
                /\ \A vt \in votes[a] : vt.ballot # b
                /\ \A a2 \in Acceptor :
                       \A vt2 \in votes[a2] :
                          (vt2.ballot = b) => (vt2.value = v)
                /\ Safe(v, b)
                /\ votes'   = [votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b, value |-> v] }]
                /\ promise' = [promise EXCEPT ![a] = b]

Next == \/ IncreasePromise \/ CastVote

Spec == Init /\ [][Next]_<<votes, promise>>

AllVotesSafe ==
    \A a \in Acceptor :
        \A vt \in votes[a] :
            Safe(vt.value, vt.ballot)

AtMostOneValuePerBallot ==
    \A b \in Ballot :
        \E v \in Value :
            \A a \in Acceptor :
                \A vt \in votes[a] :
                    vt.ballot = b => vt.value = v

TypeOk ==
    /\ votes \in [Acceptor -> SUBSET Vote]
    /\ promise \in [Acceptor -> Int]

Inv == AllVotesSafe /\ AtMostOneValuePerBallot /\ TypeOk

Chosen(v) ==
    \E b \in Ballot :
        \E Q \in Quorum :
            \A a \in Q :
                \E vt \in votes[a] :
                    vt.ballot = b /\ vt.value = v

ConsensusSpecBar ==
    \A v1_ , v2_ \in Value :
        (Chosen(v1_) /\ Chosen(v2_)) => v1_ = v2_

IsPermutation(p) ==
    /\ DOMAIN p = Acceptor
    /\ \A a \in Acceptor : p[a] \in Acceptor
    /\ \A a1, a2 \in Acceptor : p[a1] = p[a2] => a1 = a2
    /\ \A b \in Acceptor : \E a \in Acceptor : p[a] = b

MCSymmetry == { p \in [Acceptor -> Acceptor] : IsPermutation(p) }

====