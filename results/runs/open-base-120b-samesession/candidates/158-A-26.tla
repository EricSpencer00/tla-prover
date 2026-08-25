---- MODULE Voting ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    a1, a2, a3,          \* individual acceptor identifiers (may be used in cfg)
    v1, v2,              \* individual value identifiers (may be used in cfg)
    Acceptor,            \* the set of all acceptors
    Value,               \* the set of all values
    Quorum,              \* the set of quorums (each quorum is a subset of Acceptor)
    Ballot               \* the set of ballot numbers (natural numbers)

\* ----------------------------------------------------------------------
\* Operators that the configuration file substitutes for the constants
\* ----------------------------------------------------------------------
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    Votes,      \* [a \in Acceptor -> SUBSET [ballot : Ballot, value : Value]]
    Threshold   \* [a \in Acceptor -> Int]   (initially -1)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* A vote is a record with fields ballot and value
Vote == [ballot : Ballot, value : Value]

\* Safety of a value v at ballot b:
\* for every lower ballot c < b there exists a quorum Q such that each
\* member of Q either has already voted v in c or can never vote in c
Safe(v, b) ==
    \A c \in Ballot :
        (c < b) =>
            \E Q \in Quorum :
                \A a \in Q :
                    ( \E vv \in Votes[a] : vv.ballot = c /\ vv.value = v )
                    \/ ( Threshold[a] > c )

\* A value v is chosen if some quorum has all its members voting v
\* (in the same ballot, but the ballot is not important for the property)
Chosen(v) ==
    \E b \in Ballot :
        \E Q \in Quorum :
            \A a \in Q :
                \E vv \in Votes[a] :
                    /\ vv.ballot = b
                    /\ vv.value = v

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Votes = [a \in Acceptor |-> {}]
    /\ Threshold = [a \in Acceptor |-> -1]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. An acceptor may raise its promise threshold
Promise ==
    \E a \in Acceptor :
        \E b \in Ballot :
            /\ b > Threshold[a]
            /\ Threshold' = [Threshold EXCEPT ![a] = b]
            /\ UNCHANGED Votes

\* 2. An acceptor votes for a value in a ballot
VoteAction ==
    \E a \in Acceptor :
        \E b \in Ballot :
            \E v \in Value :
                /\ b >= Threshold[a]                         \* not below current promise
                /\ ~(\E vv \in Votes[a] : vv.ballot = b)    \* has not voted in this ballot yet
                /\ \A a2 \in Acceptor :
                       \A vv \in Votes[a2] :
                           (vv.ballot = b) => (vv.value = v)   \* no other value in same ballot
                /\ Safe(v, b)                                 \* safety condition
                /\ Votes' = [Votes EXCEPT ![a] = Votes[a] \cup { [ballot |-> b, value |-> v] }]
                /\ Threshold' = [Threshold EXCEPT ![a] = b]

Next ==
    \/ Promise
    \/ VoteAction

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<Votes, Threshold>>

\* ----------------------------------------------------------------------
\* Invariant
\* ----------------------------------------------------------------------
\* Type correctness of votes and thresholds
TypeInv ==
    /\ \A a \in Acceptor : Votes[a] \subseteq [ballot : Ballot, value : Value]
    /\ \A a \in Acceptor : Threshold[a] \in Int
    /\ \A a \in Acceptor : Threshold[a] >= -1

\* At most one value per ballot across all acceptors
OneValuePerBallot ==
    \A b \in Ballot :
        \A a1, a2 \in Acceptor :
            \A vv1 \in Votes[a1] , vv2 \in Votes[a2] :
                (vv1.ballot = b /\ vv2.ballot = b) => (vv1.value = vv2.value)

Inv ==
    TypeInv /\ OneValuePerBallot

\* ----------------------------------------------------------------------
\* Safety property: at most one value can be chosen
\* ----------------------------------------------------------------------
ConsensusSpecBar ==
    \A v1, v2 \in Value :
        (Chosen(v1) /\ Chosen(v2)) => v1 = v2

\* ----------------------------------------------------------------------
\* Symmetry set (trivial identity symmetry)
\* ----------------------------------------------------------------------
MCSymmetry == { [a \in Acceptor |-> a] }

\* ----------------------------------------------------------------------
\* THEOREMS (optional, can be used by model checker)
\* ----------------------------------------------------------------------
THEOREM Spec => []Inv
THEOREM Spec => []ConsensusSpecBar

====