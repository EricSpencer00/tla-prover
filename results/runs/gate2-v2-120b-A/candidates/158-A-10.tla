---- MODULE Voting ----
EXTENDS Naturals, TLC

\* ----------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANT Acceptor
CONSTANT Value
CONSTANT Quorum
CONSTANT Ballot

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Vote == [b : Ballot, v : Value]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES votes, prom

\* ----------------------------------------------------------------------
\* Type correctness (not the safety invariant, just to keep TLC happy)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ votes \in [Acceptor -> SUBSET Vote]
    /\ prom \in [Acceptor -> Ballot]

\* ----------------------------------------------------------------------
\* Safety invariant (the one required in the .cfg)
\* ----------------------------------------------------------------------
Inv ==
    /\ TypeOK
    /\ \A a \in Acceptor: prom[a] >= -1
    /\ \A a \in Acceptor: \A v \in votes[a] : v.b >= prom[a]    \* votes respect the promise

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* A quorum is safe for value v at ballot b iff for every lower ballot c,
\* there exists a quorum in which each member either has already voted for v
\* in c or cannot vote in c because its promise is > c.
SafeValue(v, b) ==
    \A c \in 0..(b - 1) :
        \E Q \in Quorum :
            \A a \in Q :
                ( [b : c, v : v] \in votes[a] ) \/ ( prom[a] > c )

\* No other value has been voted for in the same ballot
BallotUnique(b) ==
    \A a1, a2 \in Acceptor :
       \A v1, v2 \in Value :
          ( [b : b, v : v1] \in votes[a1] /\ [b : b, v : v2] \in votes[a2] ) => v1 = v2

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ prom  = [a \in Acceptor |-> -1]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. RaisePromise – an acceptor may increase its promise threshold
RaisePromise ==
    \E a \in Acceptor :
        \E nb \in Ballot :
            /\ nb > prom[a]
            /\ prom' = [prom EXCEPT ![a] = nb]
            /\ UNCHANGED votes

\* 2. CastVote – an acceptor votes for a value in a ballot
CastVote ==
    \E a \in Acceptor :
        \E b \in Ballot :
            \E v \in Value :
                /\ b >= prom[a]                           \* not below current promise
                /\ ~([b : b, v : v] \in votes[a])         \* hasn't already voted in this ballot
                /\ BallotUnique(b)                        \* no other value voted in this ballot
                /\ SafeValue(v, b)                        \* value is safe at this ballot
                /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [b |-> b, v |-> v] }]
                /\ prom'  = [prom  EXCEPT ![a] = b]

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == \/ RaisePromise
        \/ CastVote

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<votes, prom>>

\* ----------------------------------------------------------------------
\* Derived property: consensus (one chosen value at most)
\* ----------------------------------------------------------------------
ChosenValues ==
    { v \in Value :
        \E b \in Ballot :
            \E Q \in Quorum :
                \A a \in Q : [b : b, v : v] \in votes[a] }

ConsensusSpecBar == Cardinality(ChosenValues) <= 1

====