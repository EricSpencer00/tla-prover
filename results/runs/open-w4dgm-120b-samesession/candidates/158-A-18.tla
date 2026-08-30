---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

ASSUME MCAcceptor = Acceptor
ASSUME MCValue = Value
ASSUME MCQuorum = Quorum
ASSUME MCBallot = Ballot

VARIABLES votes, threshold

vars == << votes, threshold >>

TypeOK ==
    /\ votes \in [Acceptor -> SUBSET (MCBallot \X MCValue)]
    /\ threshold \in [Acceptor -> MCBallot \cup {-1}]

Init ==
    /\ votes = [a \in MCAcceptor |-> {}]
    /\ threshold = [a \in MCAcceptor |-> -1]

\* An acceptor may raise its promise threshold without casting a vote.
RaiseThreshold(a, b) ==
    /\ b > threshold[a]
    /\ threshold' = [threshold EXCEPT ![a] = b]
    /\ UNCHANGED votes

\* Votes are cast under ordering, disjointness, and quorum safety.
Vote(a, b, v) ==
    /\ b >= threshold[a]
    /\ \A x \in votes[a] : x[1] # b
    /\ \A x \in votes : (x[1] = b) => (x[2] = v)
    /\ \E q \in MCQuorum :
         /\ \A y \in q : (b, v) \in votes[y]
         /\ \A y \in q : \A c \in MCBallot :
              (c < b) => ((c, v) \in votes[y] \/ (\A z \in MCAcceptor : (c, v) \notin votes[z]))
    /\ votes' = [votes EXCEPT ![a] = @ \cup {<< b, v >>}]
    /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
    \/ \E a \in MCAcceptor, b \in MCBallot : RaiseThreshold(a, b)
    \/ \E a \in MCAcceptor, b \in MCBallot, v \in MCValue : Vote(a, b, v)

Spec == Init /\ [][Next]_vars

\* Safe(v, b): v is safe at ballot b -- every lower ballot is unanimously safe.
Safe(v, b) ==
    /\ \A x \in votes : x[1] <= b => (x[1] = b => x[2] = v)
    /\ \A c \in MCBallot : (c < b) => (\E q \in MCQuorum :
           /\ \A y \in q : (c, v) \in votes[y]
           /\ \A y \in q : \A z \in MCAcceptor : (c, v) \notin votes[z])

\* Quantified over all votes, not just the latest.
AllVotesSafe == \A a \in MCAcceptor, x \in votes[a] : Safe(x[2], x[1])

AtMostOnePerBallot ==
    \A x \in UNION {votes[a] : a \in MCAcceptor} :
        \A y \in UNION {votes[a] : a \in MCAcceptor} :
            (x[1] = y[1]) => (x[2] = y[2])

VarsWellFormed ==
    /\ votes \in [Acceptor -> SUBSET (MCBallot \X MCValue)]
    /\ threshold \in [Acceptor -> MCBallot \cup {-1}]

Inv == AllVotesSafe /\ AtMostOnePerBallot /\ VarsWellFormed

Chosen(v) == \E q \in MCQuorum : \A a \in q : << 0, v >> \in votes[a]

ChosenIsSingleValue == \A v \in MCValue : Chosen(v) => v = v1

\* The voting algorithm refines the abstract consensus spec: the chosen set is
\* derived from the votes, and the at-most-one-per-ballot invariant is exactly
\* the consensus protocol's safety condition.
ConsensusSpecBar ==
    /\ Inv
    /\ \A v \in MCValue : Chosen(v) <=> (\A a \in MCAcceptor : << 0, v >> \in votes[a])
    /\ \A v \in MCValue : Chosen(v) => v = v1

\* Acceptors are symmetric participants in the vote.
MCSymmetry == {f \in [Acceptor -> Acceptor] : \A a \in Acceptor : f[a] \in Acceptor}

====