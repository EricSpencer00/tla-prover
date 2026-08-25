---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS 
    a1, a2, a3,               \* individual acceptor identifiers
    v1, v2,                   \* individual value identifiers
    Acceptor, Value, Quorum, Ballot

\*-------------------------------------------------
\* Operators used for model checking symmetry and
\* constant substitution
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\*-------------------------------------------------
\* State variables
VARIABLES Votes, Threshold

\*-------------------------------------------------
\* Types
TypeCorrect ==
    /\ Votes \in [Acceptor -> SUBSET [ballot: Ballot, value: Value]]
    /\ Threshold \in [Acceptor -> Int]

\*-------------------------------------------------
\* Safety predicate for a value at a ballot
Safe(v, b) ==
    \A c \in Ballot :
        (c < b) =>
            \E q \in Quorum :
                \A a \in q :
                    ( [ballot |-> c, value |-> v] \in Votes[a] )
                    \/ (Threshold[a] > c)

\*-------------------------------------------------
\* All votes cast are safe
SafeVotes ==
    \A a \in Acceptor :
        \A vt \in Votes[a] :
            Safe(vt.value, vt.ballot)

\*-------------------------------------------------
\* At most one value per ballot across all acceptors
OneValuePerBallot ==
    \A b \in Ballot :
        \A v1, v2 \in Value :
            ( (\E a1 \in Acceptor : [ballot |-> b, value |-> v1] \in Votes[a1])
              /\ (\E a2 \in Acceptor : [ballot |-> b, value |-> v2] \in Votes[a2]) )
            => v1 = v2

\*-------------------------------------------------
\* Invariant
Inv == TypeCorrect /\ SafeVotes /\ OneValuePerBallot

\*-------------------------------------------------
\* Initial state
Init ==
    /\ Votes = [a \in Acceptor |-> {}]
    /\ Threshold = [a \in Acceptor |-> -1]

\*-------------------------------------------------
\* Promise action: raise the promise threshold
Promise ==
    \E a \in Acceptor :
        \E b \in Ballot :
            /\ b > Threshold[a]
            /\ Votes' = Votes
            /\ Threshold' = [Threshold EXCEPT ![a] = b]

\*-------------------------------------------------
\* Vote action: cast a vote for a value in a ballot
Vote ==
    \E a \in Acceptor :
        \E b \in Ballot :
            \E v \in Value :
                /\ b >= Threshold[a]                              \* not below promise
                /\ ~(\E vv \in Value : [ballot |-> b, value |-> vv] \in Votes[a])
                                                            \* a has not voted in this ballot yet
                /\ \A a2 \in Acceptor :
                        ( \E vv \in Value : [ballot |-> b, value |-> vv] \in Votes[a2] )
                        => (\E vv \in Value :
                                [ballot |-> b, value |-> vv] \in Votes[a2] /\ vv = v)
                                                            \* no different value already voted in this ballot
                /\ Safe(v, b)                                     \* value is safe at this ballot
                /\ Votes' = [Votes EXCEPT ![a] = Votes[a] \cup { [ballot |-> b, value |-> v] }]
                /\ Threshold' = [Threshold EXCEPT ![a] = b]

\*-------------------------------------------------
\* Next-state relation
Next == \/ Promise \/ Vote

\*-------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<Votes, Threshold>>

\*-------------------------------------------------
\* Definition of chosen values
Chosen == { v \in Value :
                \E b \in Ballot :
                    \E q \in Quorum :
                        \A a \in q :
                            [ballot |-> b, value |-> v] \in Votes[a] }

\*-------------------------------------------------
\* Consensus safety property
ConsensusSpecBar == \A v1, v2 \in Chosen : v1 = v2

\*-------------------------------------------------
\* Symmetry set (identity permutation suffices)
MCSymmetry == { [a \in Acceptor |-> a] }

====