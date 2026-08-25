---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, TLC

\*-------------------------------
\* Constants (to be instantiated in the .cfg)
\*-------------------------------
CONSTANT a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\*-------------------------------
\* Derived finite versions for model checking
\*-------------------------------
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\*-------------------------------
\* State variables
\*-------------------------------
VARIABLES votes, thresh

\* votes[ a ]  : the set of (ballot, value) pairs that acceptor a has cast
\* thresh[ a ] : the current promise threshold of acceptor a (integer, -1 means no promise)
\*-------------------------------
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ thresh = [a \in Acceptor |-> -1]

\*-------------------------------
\* Helper definitions
\*-------------------------------
BallotSet == Ballot \cup {-1}

\* A quorum is any element of the constant set Quorum
IsQuorum(Q) == Q \in Quorum

\* Overlap property (assumed for the model, not enforced here)
QuorumOverlap ==
    \A Q1, Q2 \in Quorum : Q1 # Q2 => Q1 \cap Q2 # {}

\* Safety of a vote (b,v) according to the description
Safe(b, v) ==
    \A c \in Ballot :
        (c < b) =>
            \E Q \in Quorum :
                \A a \in Q :
                    ( (c, v) \in votes[a] ) \/ ( thresh[a] > c )

\* At most one value per ballot across all acceptors
OneValuePerBallot ==
    \A b \in Ballot :
        \A a1, a2 \in Acceptor :
            \A v1, v2 \in Value :
                ( (b, v1) \in votes[a1] /\ (b, v2) \in votes[a2] ) => v1 = v2

\* Type correctness invariant
TypeCorrect ==
    /\ \A a \in Acceptor : votes[a] \subseteq Ballot \X Value
    /\ \A a \in Acceptor : thresh[a] \in BallotSet

\* Every vote that has been cast is safe
AllVotesSafe ==
    \A a \in Acceptor :
        \A <<b, v>> \in votes[a] :
            Safe(b, v)

\*-------------------------------
\* Actions
\*-------------------------------
Promise(a, b) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ b > thresh[a]
    /\ UNCHANGED votes
    /\ thresh' = [thresh EXCEPT ![a] = b]

Vote(a, b, v) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ v \in Value
    /\ b >= thresh[a]                 \* cannot vote below current promise
    /\ ~(\E <<b2, _>> \in votes[a] : b2 = b)   \* no prior vote in this ballot
    /\ \A a2 \in Acceptor :
           \A v2 \in Value :
               ( (b, v2) \in votes[a2] ) => v2 = v   \* no other value already voted in this ballot
    /\ Safe(b, v)                     \* safety condition
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
    /\ thresh' = [thresh EXCEPT ![a] = b]

Next ==
    \E a \in Acceptor :
        \E b \in Ballot :
            ( Promise(a, b) \/ \E v \in Value : Vote(a, b, v) )

\*-------------------------------
\* Specification
\*-------------------------------
Spec == Init /\ [][Next]_<<votes, thresh>>

\*-------------------------------
\* Invariant
\*-------------------------------
Inv == /\ TypeCorrect
       /\ AllVotesSafe
       /\ OneValuePerBallot

\*-------------------------------
\* Chosen values and Consensus property
\*-------------------------------
Chosen ==
    { v \in Value :
        \E b \in Ballot :
          \E Q \in Quorum :
            (\A a \in Q : <<b, v>> \in votes[a]) }

ConsensusSpecBar == 
    \A v1, v2 \in Value :
        ( v1 \in Chosen /\ v2 \in Chosen ) => v1 = v2

\*-------------------------------
\* Symmetry definition for model checking
\*-------------------------------
MCSymmetry ==
    { p \in [Acceptor -> Acceptor] :
        /\ \A a \in Acceptor : p[a] \in Acceptor
        /\ \A a1, a2 \in Acceptor : p[a1] = p[a2] => a1 = a2 }

====