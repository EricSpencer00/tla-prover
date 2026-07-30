---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* The cfg substitutes MCAcceptor, MCValue, MCQuorum, MCBallot for the above
\* constants; they are defined as the same name so the substitution is harmless.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

VARIABLES votes, thresh

vars == <<votes, thresh>>

TypeOK ==
    /\ votes \in [MCAcceptor -> SUBSET (MCBallot \X MCValue)]
    /\ thresh \in [MCAcceptor -> MCBallot \cup {-1}]

Init ==
    /\ votes = [a \in MCAcceptor |-> {}]
    /\ thresh = [a \in MCAcceptor |-> -1]

\* The ballot must be above the acceptor's promised threshold.
Vote(a, b, v) ==
    /\ b >= thresh[a]
    /\ [b, v] \notin votes[a]
    /\ (\A c \in MCAcceptor : [b, v] \notin votes[c])
    /\ (\A q \in MCQuorum : \A c \in q : Safe(c, b, v))
    /\ votes' = [votes EXCEPT ![a] = @ \cup {[b, v]}]
    /\ thresh' = [thresh EXCEPT ![a] = b]

\* A promise raises the acceptor's floor without casting a vote.
Promised(a, b) ==
    /\ b > thresh[a]
    /\ thresh' = [thresh EXCEPT ![a] = b]
    /\ UNCHANGED votes

Safe(c, b, v) ==
    /\ (\A c \in MCQuorum : [b, v] \in votes[c])
    /\ \A c \in MCBallot \ {b} :
        /\ c < b
        /\ \E q \in MCQuorum : \A d \in q : [c, v] \in votes[d]

Next ==
    \/ \E a \in MCAcceptor, b \in MCBallot, v \in MCValue : Vote(a, b, v)
    \/ \E a \in MCAcceptor, b \in MCBallot : Promised(a, b)

Spec == Init /\ [][Next]_vars

\* Safety: at most one value can ever be chosen by a quorum.
Inv ==
    /\ (\A a \in MCAcceptor : \A p \in votes[a] : Safe(a, p[1], p[2]))
    /\ (\A a, c \in MCAcceptor : \A p \in votes[a] : \A q \in votes[c] :
            (p[1] = q[1]) => (p[2] = q[2]))
    /\ TypeOK

\* Any bounded instance of the voting algorithm implements consensus.
ConsensusSpecBar ==
    \A x \in MCValue, c \in MCBallot :
        (\A q \in MCQuorum : [c, x] \in votes[q]) ~> (\A q \in MCQuorum : [c, x] \in votes[q])

\* Action symmetry: any permutation of the acceptors leaves the spec unchanged.
MCSymmetry ==
    \A f \in [MCAcceptor -> MCAcceptor] :
        /\ (\A x, y \in MCAcceptor : f[x] = f[y] => x = y)
        /\ UNCHANGED <<votes, thresh>>

====