---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

VARIABLES votes, threshold
vars == <<votes, threshold>>

Cast == {<<a, b, v>> : a \in Acceptor, b \in Ballot, v \in Value}

TypeOK ==
    /\ votes \subseteq Cast
    /\ threshold \in [Acceptor -> (Ballot \cup {-1})]

Init ==
    /\ votes = {}
    /\ threshold = [a \in Acceptor |-> -1]

Voter == {a \in Acceptor : <<a, b, v>> \in votes}
VotedFor(v) == {a \in Acceptor : <<a, b, v>> \in votes}
BallotOf(a) == CHOOSE b \in Ballot : <<a, b, v1>> \in votes \/ <<a, b, v2>> \in votes

SafetyCondition(v, b) ==
    \A c \in Ballot :
        (c < b) => \E q \in Quorum :
            \A x \in q : (<<x, c, v>> \in votes) \/ (~\E w \in Value : <<x, c, w>> \in votes)

Vote(a, b, v) ==
    /\ threshold[a] <= b
    /\ ~\E c \in Ballot : <<a, c, v>> \in votes
    /\ \A w \in Value : (w # v) => ~\E c \in Ballot : <<a, c, w>> \in votes
    /\ \E q \in Quorum : \A x \in q : (Voter \cap q = {x}) => ~\E w \in Value : <<x, b, w>> \in votes
    /\ SafetyCondition(v, b)
    /\ votes' = votes \cup {<<a, b, v>>}
    /\ threshold' = [threshold EXCEPT ![a] = b]

Promise(a, b) ==
    /\ b > threshold[a]
    /\ threshold' = [threshold EXCEPT ![a] = b]
    /\ UNCHANGED votes

Next ==
    \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)
    \/ \E a \in Acceptor, b \in Ballot : Promise(a, b)

Spec == Init /\ [][Next]_vars

Inv ==
    /\ \A e \in votes : SafetyCondition(e[3], e[2])
    /\ \A e1, e2 \in votes : (e1[2] = e2[2]) => (e1[3] = e2[3])
    /\ TypeOK

ConsensusSpecBar ==
    /\ Inv
    /\ \A a \in Acceptor : threshold[a] <= (CHOOSE b \in Ballot : TRUE)
    /\ UNCHANGED vars

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

MCSymmetry == (<<a1, a2, a3>> :> <<a1, a3, a2>>) @@ (<<a1, a2, a3>> :> <<a2, a1, a3>>)
====