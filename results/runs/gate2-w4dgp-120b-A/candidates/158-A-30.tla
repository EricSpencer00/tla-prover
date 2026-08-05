---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

MCAcceptor == {a1, a2, a3}
MCValue == {v1, v2}
MCQuorum == {Q1, Q2}
MCBallot == {b1, b2}
Q1 == {a1, a2}
Q2 == {a2, a3}

VARIABLES cast, thresh

vars == <<cast, thresh>>

Votes == [ball : MCBallot, val : MCValue]

TypeOK ==
    /\ cast \in [MCAcceptor -> SUBSET Votes]
    /\ thresh \in [MCAcceptor -> MCBallot \cup {-1}]

QuorumsOverlap ==
    \A q1 \in MCQuorum, q2 \in MCQuorum : q1 # q2 => (q1 \cap q2) # {}

NoSameBallotDiffValue ==
    \A a \in MCAcceptor, b \in MCBallot, v \in MCValue :
        <<b, v>> \in cast[a] =>
            \A w \in MCValue : <<b, w>> \in cast[a] => w = v

NoDoubleVote ==
    \A a \in MCAcceptor, b \in MCBallot :
        \A v, w \in MCValue :
            (<<b, v>> \in cast[a] /\ <<b, w>> \in cast[a]) => v = w

Init ==
    /\ cast = [a \in MCAcceptor |-> {}]
    /\ thresh = [a \in MCAcceptor |-> -1]

Promised(a, b, v) ==
    /\ b >= thresh[a]
    /\ (b, v) \notin cast[a]
    /\ \A b2 \in MCBallot, w \in MCValue :
        (b2 < b /\ <<b2, w>> \in cast[a]) => w = v
    /\ \A a2 \in MCAcceptor : (b, v) \in cast[a2] => a2 = a
    /\ \E q \in MCQuorum :
        \A a2 \in q :
            (b, v) \in cast[a2] \/ (\A c \in MCBallot :
                c < b => (c, v) \notin cast[a2])

Vote(a, b, v) ==
    /\ Promised(a, b, v)
    /\ cast' = [cast EXCEPT ![a] = cast[a] \cup {<<b, v>>}]
    /\ thresh' = [thresh EXCEPT ![a] = b]
    /\ UNCHANGED <<>>

RaiseThresh(a, b) ==
    /\ b >= thresh[a]
    /\ thresh[a] # b
    /\ thresh' = [thresh EXCEPT ![a] = b]
    /\ UNCHANGED <<cast>>

Next ==
    \/ \E a \in MCAcceptor, b \in MCBallot, v \in MCValue : Vote(a, b, v)
    \/ \E a \in MCAcceptor, b \in MCBallot : RaiseThresh(a, b)

Spec == Init /\ [][Next]_vars

VoteBallot == {b \in MCBallot : \E a \in MCAcceptor, v \in MCValue : <<b, v>> \in cast[a]}
Chosen == {v \in MCValue : \E q \in MCQuorum :
    \E b \in MCBallot : \A a \in q : <<b, v>> \in cast[a]}

Inv ==
    /\ TypeOK
    /\ QuorumsOverlap
    /\ NoSameBallotDiffValue
    /\ NoDoubleVote
    /\ Cardinals == Cardinality(Votes) <= Cardinality(MCBallot) + 1

ConsensusSpecBar == Cardinality(Chosen) <= 1

MCSymmetry == {f \in [MCAcceptor -> MCAcceptor] : \A a \in MCAcceptor : f[f[a]] = a}
====