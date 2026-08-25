---- MODULE Voting ----
EXTENDS Naturals, Integers, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\*--------------------------------------------------------------------
\* State variables
\*--------------------------------------------------------------------
VARIABLES votes, thresh

\*--------------------------------------------------------------------
\* Helper definitions
\*--------------------------------------------------------------------
Safe(v, b) == 
    \A c \in Ballot :
        (c < b) => 
            \E Q \in Quorum :
                /\ Q \subseteq Acceptor
                /\ \A a \in Q :
                       ( [ballot |-> c, value |-> v] \in votes[a] ) \/ (thresh[a] > c)

OneValuePerBallot == 
    \A b \in Ballot :
        \A a1, a2 \in Acceptor :
            \A v1, v2 \in Value :
                ( [ballot |-> b, value |-> v1] \in votes[a1] /\ 
                  [ballot |-> b, value |-> v2] \in votes[a2] ) => v1 = v2

AllVotesSafe == 
    \A a \in Acceptor :
        \A vv \in votes[a] :
            Safe(vv.value, vv.ballot)

TypeOk == 
    /\ votes \in [Acceptor -> SUBSET [ballot: Ballot, value: Value]]
    /\ thresh \in [Acceptor -> Int]

\*--------------------------------------------------------------------
\* Invariant
\*--------------------------------------------------------------------
Inv == 
    /\ TypeOk
    /\ OneValuePerBallot
    /\ AllVotesSafe

\*--------------------------------------------------------------------
\* Initialization
\*--------------------------------------------------------------------
Init == 
    /\ votes = [a \in Acceptor |-> {}]
    /\ thresh = [a \in Acceptor |-> -1]

\*--------------------------------------------------------------------
\* Actions
\*--------------------------------------------------------------------
Promise == 
    \E a \in Acceptor : \E b \in Ballot :
        /\ b > thresh[a]
        /\ UNCHANGED votes
        /\ thresh' = [thresh EXCEPT ![a] = b]

Vote == 
    \E a \in Acceptor : \E b \in Ballot : \E v \in Value :
        /\ b >= thresh[a]
        /\ ~(\E vv \in votes[a] : vv.ballot = b)               \* no prior vote in this ballot
        /\ (\A a2 \in Acceptor : \A vv \in votes[a2] :
                vv.ballot = b => vv.value = v)                \* same value for this ballot
        /\ Safe(v, b)
        /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b, value |-> v] }]
        /\ thresh' = [thresh EXCEPT ![a] = b]

Next == Promise \/ Vote

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_<<votes, thresh>>

\*--------------------------------------------------------------------
\* Safety property (consensus)
\*--------------------------------------------------------------------
ConsensusSpecBar == 
    [] ( \A Q1 \in Quorum : \A b1 \in Ballot : \A v1 \in Value :
            ( \A a \in Q1 : [ballot |-> b1, value |-> v1] \in votes[a] ) =>
            \A Q2 \in Quorum : \A b2 \in Ballot : \A v2 \in Value :
                ( \A a \in Q2 : [ballot |-> b2, value |-> v2] \in votes[a] ) => v1 = v2)

\*--------------------------------------------------------------------
\* Symmetry (identity permutation)
\*--------------------------------------------------------------------
MCSymmetry == { [a \in Acceptor |-> a] }

\*--------------------------------------------------------------------
\* Operators overridden by the model checker
\*--------------------------------------------------------------------
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

====