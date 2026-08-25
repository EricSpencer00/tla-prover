---- MODULE Voting ----
EXTENDS Naturals, Integers, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* CONSTANTS (instantiated by the .cfg file)
\* ----------------------------------------------------------------------
CONSTANT a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES votes, threshold

\* ----------------------------------------------------------------------
\* Type definitions
\* ----------------------------------------------------------------------
VoteRec == [ballot : Ballot, value : Value]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> -1]

\* ----------------------------------------------------------------------
\* Safety predicate
\* ----------------------------------------------------------------------
Safe(v, b) ==
    \A c \in Ballot :
        (c < b) =>
            \E Q \in Quorum :
                \A a \in Q :
                    ( [ballot |-> c, value |-> v] \in votes[a] )
                    \/ (threshold[a] > c)

\* ----------------------------------------------------------------------
\* Action: an acceptor raises its promise threshold
\* ----------------------------------------------------------------------
Promise(a, b) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ b > threshold[a]
    /\ UNCHANGED votes
    /\ threshold' = [threshold EXCEPT ![a] = b]

\* ----------------------------------------------------------------------
\* Action: an acceptor casts a vote
\* ----------------------------------------------------------------------
Vote(a, b, v) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ v \in Value
    /\ b >= threshold[a]                     \* cannot vote below promise
    /\ \A a2p \in Acceptor :
          ( [ballot |-> b, value |-> v] \in votes[a2p] ) \/ 
          (\A w \in Value : [ballot |-> b, value |-> w] \notin votes[a2p])  \* no different value already voted
    /\ ~(\E w \in Value : [ballot |-> b, value |-> w] \in votes[a])  \* a has not voted in b yet
    /\ Safe(v, b)                            \* value is safe at ballot b
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b, value |-> v] }]
    /\ threshold' = [threshold EXCEPT ![a] = b]

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E a \in Acceptor, b \in Ballot : Promise(a, b)
    \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<votes, threshold>>

\* ----------------------------------------------------------------------
\* Type‑correctness invariant
\* ----------------------------------------------------------------------
TypeCorrect ==
    /\ \A a \in Acceptor :
          votes[a] \subseteq { r \in VoteRec : TRUE }
    /\ \A a \in Acceptor : threshold[a] \in Int

\* ----------------------------------------------------------------------
\* All votes are safe
\* ----------------------------------------------------------------------
AllVotesSafe ==
    /\ \A a \in Acceptor :
         \A vRec \in votes[a] :
             Safe(vRec.value, vRec.ballot)

\* ----------------------------------------------------------------------
\* At most one value per ballot
\* ----------------------------------------------------------------------
OneValuePerBallot ==
    /\ \A b \in Ballot :
          \A aA, aB \in Acceptor :
            \A val1, val2 \in Value :
               ( [ballot |-> b, value |-> val1] \in votes[aA] /\ 
                 [ballot |-> b, value |-> val2] \in votes[aB] ) => val1 = val2

\* ----------------------------------------------------------------------
\* Global invariant
\* ----------------------------------------------------------------------
Inv == TypeCorrect /\ AllVotesSafe /\ OneValuePerBallot

\* ----------------------------------------------------------------------
\* Definition of a chosen value
\* ----------------------------------------------------------------------
Chosen(v) ==
    \E b \in Ballot, Q \in Quorum :
        \A a \in Q :
            [ballot |-> b, value |-> v] \in votes[a]

\* ----------------------------------------------------------------------
\* Consensus safety property
\* ----------------------------------------------------------------------
ConsensusSpecBar == [] ( \A val1, val2 \in Value :
                         (Chosen(val1) /\ Chosen(val2)) => val1 = val2 )
====