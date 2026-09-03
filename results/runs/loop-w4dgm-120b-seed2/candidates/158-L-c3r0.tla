---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

Operators == [ball : Ballot, val : Value]

VARIABLES votes, promised

vars == <<votes, promised>>

TypeOK ==
    /\ votes \in [Acceptor -> SUBSET Operators]
    /\ promised \in [Acceptor -> Ballot \cup {-1}]

Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ promised = [a \in Acceptor |-> -1]

\* An acceptor may raise its promise threshold to rule out voting in earlier
\* ballots; this is the only way an acceptor's future participation changes.
RaiseThreshold(a, v) ==
    /\ v \in Ballot
    /\ v > promised[a]
    /\ promised' = [promised EXCEPT ![a] = v]
    /\ UNCHANGED votes

\* An acceptor votes for a value in a ballot once no other value has been
\* voted for in that same ballot and the value is safe at that ballot.
Vote(a, v, val) ==
    /\ \A o \in votes[a] : v >= o.ball
    /\ \A o \in votes[a] : o.ball # v
    /\ \A b \in Acceptor : (v \in votes[b]) => (votes[b][v].val = val)
    /\ \E Q \in Quorum :
         \A c \in 0 .. (v - 1) :
            \A b \in Q : \E val2 \in Value : [ball |-> c, val |-> val2] \in votes[b] \/ promised[b] >= c
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {[ball |-> v, val |-> val]}}
    /\ promised' = [promised EXCEPT ![a] = v]

Next ==
    \/ \E a \in Acceptor, v \in Ballot : RaiseThreshold(a, v)
    \/ \E a \in Acceptor, v \in Ballot, val \in Value : Vote(a, v, val)

Spec == Init /\ [][Next]_vars

\* Every cast vote must be safe at its own ballot number, which forces it to
\* agree with the lower-ballot picture of reality.
VotedIsSafe ==
    \A a \in Acceptor, o \in votes[a] :
        \A c \in 0 .. (o.ball - 1) :
            \E Q \in Quorum : \A b \in Q : \E val2 \in Value : [ball |-> c, val |-> val2] \in votes[b]

\* At most one value is ever voted for in a given ballot across all acceptors.
BallotConsistent ==
    \A a, b \in Acceptor : \A o1, o2 \in votes[a] \cap votes[b] : o1.ball = o2.ball => o1.val = o2.val

Inv == VotedIsSafe /\ BallotConsistent /\ TypeOK

\* The derived consensus spec: a value is considered chosen once a quorum has
\* voted for it in some ballot, and no two different values can both be chosen.
ConsensusSpecBar ==
    \A val \in Value :
        ((\E Q \in Quorum : \A b \in Q : [ball |-> 0, val |-> val] \in votes[b])
           => (\A Q \in Quorum : \A b \in Q : [ball |-> 0, val |-> val] \in votes[b]))

MCSymmetry == {}

\* The .cfg substitutes the following bounded constants for the abstract ones.
MCAcceptor == {a1, a2, a3}
MCValue == {v1, v2}
MCQuorum == { {a1, a2}, {a2, a3} }
MCBallot == {0, 1}

====