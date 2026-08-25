---- MODULE Voting ----
EXTENDS Naturals, Integers, TLC

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

(* aliases that the .cfg file may substitute *)
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

VARIABLES Votes, Threshold

(* ------------------------------------------------------------------- *)
Init ==
    /\ Votes    = [a \in Acceptor |-> {}]
    /\ Threshold = [a \in Acceptor |-> -1]

PromiseIncrease(a, b) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ b > Threshold[a]
    /\ Threshold' = [Threshold EXCEPT ![a] = b]
    /\ UNCHANGED Votes

Vote(a, b, v) ==
    LET VotePair == <<b, v>> IN
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ v \in Value
    /\ b >= Threshold[a]                                    \* respect promise
    /\ ~(\E vp \in Votes[a] : vp[1] = b)                    \* not already voted in this ballot
    /\ \A a2 \in Acceptor: \A vp \in Votes[a2] :
           (vp[1] = b) => (vp[2] = v)                       \* no conflicting vote
    /\ Safe(v, b)
    /\ Votes'    = [Votes EXCEPT ![a] = Votes[a] \cup {VotePair}]
    /\ Threshold' = [Threshold EXCEPT ![a] = b]
    /\ UNCHANGED << >>

Safe(v, b) ==
    \A c \in Ballot :
        (c < b) =>
            \E Q \in Quorum :
                /\ Q \subseteq Acceptor
                /\ \A a \in Q :
                       (<<c, v>> \in Votes[a]) \/ (Threshold[a] > c)

AtMostOneValuePerBallot ==
    \A b \in Ballot :
        \A a1, a2 \in Acceptor :
            \A v1, v2 \in Value :
                (<<b, v1>> \in Votes[a1] /\ <<b, v2>> \in Votes[a2]) => v1 = v2

TypeInvariant ==
    /\ Votes    \in [Acceptor -> SUBSET <<Ballot, Value>>]
    /\ Threshold \in [Acceptor -> Int]

Inv ==
    /\ TypeInvariant
    /\ \A a \in Acceptor: \A vp \in Votes[a] : Safe(vp[2], vp[1])
    /\ AtMostOneValuePerBallot

Next ==
    \/ \E a \in Acceptor: \E b \in Ballot: PromiseIncrease(a, b)
    \/ \E a \in Acceptor: \E b \in Ballot: \E v \in Value: Vote(a, b, v)

Spec ==
    Init /\ [][Next]_<<Votes, Threshold>>

Chosen ==
    { v \in Value :
        \E b \in Ballot :
            \E Q \in Quorum :
                /\ Q \subseteq Acceptor
                /\ \A a \in Q : <<b, v>> \in Votes[a] }

ConsensusSpecBar ==
    \A v1, v2 \in Chosen : v1 = v2

MCSymmetry ==
    { [a \in Acceptor |-> a] }

====