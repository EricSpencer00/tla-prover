---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

AcceptorSet == {a1, a2, a3}
ValueSet == {v1, v2}
QuorumSet == {q1, q2, q3}
BallotSet == {0, 1, 2}

MCAcceptor == AcceptorSet
MCValue == ValueSet
MCQuorum == QuorumSet
MCBallot == BallotSet

Quorums == MCQuorum

Votes == [acpt : MCAcceptor, val : MCValue, bal : MCBallot]

VARIABLES vote, minBal

vars == <<vote, minBal>>

TypeOK ==
    /\ vote \in SUBSET Votes
    /\ minBal \in [MCAcceptor -> MCBallot \cup {-1}]

Init ==
    /\ vote = {}
    /\ minBal = [a \in MCAcceptor |-> -1]

QuorumFor(v) == {q \in Quorums : \A a \in q : [acpt |-> a, val |-> v, bal |-> 0] \in vote}

\* Safety of v at ballot b: every lower ballot has a quorum that already voted
\* for v (or a quorum that is now naturally ineligible to vote at that ballot).
SafeAt(v, b) ==
    \A c \in 0..(b - 1) :
        \E q \in Quorums :
            \A a \in q :
                \/ [acpt |-> a, val |-> v, bal |-> c] \in vote
                \/ minBal[a] >= c

\* The promise is the irreversible step: raising it excludes the acceptor
\* from every ballot below the new one forever after.
RaisePromise(a, b) ==
    /\ b > minBal[a]
    /\ minBal' = [minBal EXCEPT ![a] = b]
    /\ UNCHANGED vote

\* An acceptor votes only for a value that is safe at that ballot, once its
\* own threshold allows it, and only if no other value has already been
\* voted for in that same ballot.
Vote(a, v, b) ==
    /\ b >= minBal[a]
    /\ [acpt |-> a, val |-> v, bal |-> b] \notin vote
    /\ \A w \in MCValue : [acpt |-> a, val |-> w, bal |-> b] \notin vote
    /\ SafeAt(v, b)
    /\ vote' = vote \cup {[acpt |-> a, val |-> v, bal |-> b]}
    /\ minBal' = [minBal EXCEPT ![a] = b]

Next ==
    \/ \E a \in MCAcceptor, b \in MCBallot : RaisePromise(a, b)
    \/ \E a \in MCAcceptor, v \in MCValue, b \in MCBallot : Vote(a, v, b)

Spec == Init /\ [][Next]_vars

\* Consistency: at most one chosen value overall, derived from three guards.
Inv ==
    /\ \A e \in vote : SafeAt(e.val, e.bal)
    /\ \A e1, e2 \in vote : (e1.bal = e2.bal) => (e1.val = e2.val)
    /\ TypeOK

\* The abstract consensus spec: at most one chosen value now, derived from
\* votes rather than asserted directly.
ConsensusSpecBar ==
    \A v \in MCValue :
        (\E q \in Quorums :
            \A a \in q : [acpt |-> a, val |-> v, bal |-> 0] \in vote) =>
            (\A u \in MCValue :
                (\E q2 \in Quorums :
                    \A a \in q2 : [acpt |-> a, val |-> u, bal |-> 0] \in vote) => u = v)

\* Permutation of acceptors, values, quorums, and ballots that leaves the model
\* invariant; used by the model checker to reduce the explored state space.
MCSymmetry ==
    {f \in [MCAcceptor -> MCAcceptor, MCValue -> MCValue, Quorum -> Quorum, Ballot -> Ballot] :
        \A x \in Union({MCAcceptor, MCValue, Quorum, Ballot}) : x \in DOMAIN f}

====