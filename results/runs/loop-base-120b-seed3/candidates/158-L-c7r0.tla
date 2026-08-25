---- MODULE Voting ----
EXTENDS Naturals, Integers, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* CONSTANTS (instantiated by the .cfg file)
\* ----------------------------------------------------------------------
CONSTANT a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* ----------------------------------------------------------------------
\* Operators used for model checking substitution
\* ----------------------------------------------------------------------
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

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
    /\ \A a2 \in Acceptor :
          ( [ballot |-> b, value |-> v] \in votes[a2] ) \/ 
          (\A w \in Value : [ballot |-> b, value |-> w] \notin votes[a2])  \* no different value already voted
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
          \A a1, a2 \in Acceptor :
            \A v1, v2 \in Value :
               ( [ballot |-> b, value |-> v1] \in votes[a1] /\ 
                 [ballot |-> b, value |-> v2] \in votes[a2] ) => v1 = v2

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
ConsensusSpecBar == [] ( \A v1, v2 \in Value :
                         (Chosen(v1) /\ Chosen(v2)) => v1 = v2 )

\* ----------------------------------------------------------------------
\* Symmetry definition (set of all bijections on Acceptor)
\* ----------------------------------------------------------------------
IsBijective(p) ==
    /\ \A a1, a2 \in Acceptor : p[a1] = p[a2] => a1 = a2
    /\ \A a \in Acceptor : \E a2 \in Acceptor : p[a2] = a

MCSymmetry == { p \in [Acceptor -> Acceptor] : IsBijective(p) }

====