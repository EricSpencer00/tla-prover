---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

ASSUME MCAcceptor = Acceptor
ASSUME MCValue = Value
ASSUME MCQuorum = Quorum
ASSUME MCBallot = Ballot

VARIABLES votes, th

vars == <<votes, th>>

VotePairs == [ball : Ballot, val : Value]

TypeOK ==
    /\ votes \in [Acceptor -> SUBSET VotePairs]
    /\ th \in [Acceptor -> Ballot \cup {-1}]

Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ th = [a \in Acceptor |-> -1]

Voted(a, v) == \E p \in votes[a] : p.val = v

SafeAt(v, b) ==
    /\ \A a \in Acceptor : \E p \in votes[a] : p.ball = b /\ p.val = v
    /\ \A c \in Ballot : c < b => \E Q \in Quorum :
        \A a \in Q : Voted(a, v) \/ \A p \in votes[a] : p.ball # c

Increase(a, b) ==
    /\ th[a] < b
    /\ th' = [th EXCEPT ![a] = b]
    /\ UNCHANGED votes

Vote(a, v, b) ==
    /\ th[a] < b
    /\ \A p \in votes[a] : p.ball # b
    /\ \A a2 \in Acceptor : \A p2 \in votes[a2] : p2.ball = b => p2.val = v
    /\ SafeAt(v, b)
    /\ votes' = [votes EXCEPT ![a] = @ \cup {[ball |-> b, val |-> v]}]
    /\ th' = [th EXCEPT ![a] = b]

Next ==
    \E a \in Acceptor :
        \/ \E b \in Ballot : Increase(a, b)
        \/ \E v \in Value, b \in Ballot : Vote(a, v, b)

Spec == Init /\ [][Next]_vars

Chosen == {v \in Value : \E Q \in Quorum : \A a \in Q : Voted(a, v)}

Inv ==
    /\ \A a \in Acceptor : \A p \in votes[a] : SafeAt(p.val, p.ball)
    /\ \A v1 \in Value, v2 \in Value, b \in Ballot :
           (\A a \in Acceptor : Voted(a, v1) /\ \A a \in Acceptor : Voted(a, v2) /\ b \in Ballot) => v1 = v2
    /\ TypeOK

\* The chosen value is determined by the votes recorded, so the vote-recording
\* step is the only way the chosen value can change; the threshold-only step
\* never moves anything that could affect which value is chosen.
ConsensusSpecBar == Spec /\ (vars = [votes EXCEPT ! = votes] /\ [th EXCEPT ! = th])

\* The overlap property of the quorum family is assumed here as a model
\* invariant rather than a structural fact about how Quorum is built.
MCSymmetry == TRUE

====