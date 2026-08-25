---- MODULE Voting ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\*=====================================================================
\*  Operators that the configuration substitutes for the constants
\*=====================================================================
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\*=====================================================================
\*  State variables
\*=====================================================================
VARIABLES Votes, Threshold

\*---------------------------------------------------------------------
\*  Types
\*---------------------------------------------------------------------
Vote == [ballot : Ballot, value : Value]

\*=====================================================================
\*  Initialization
\*=====================================================================
Init ==
    /\ Votes = [a \in Acceptor |-> {}]
    /\ Threshold = [a \in Acceptor |-> -1]

\*=====================================================================
\*  Safety predicate for a vote
\*=====================================================================
Safe(b, v) ==
    \A c \in Ballot :
        (c < b) => 
            \E Q \in Quorum :
                \A a \in Q :
                    ( \E vote \in Votes[a] :
                        /\ vote.ballot = c
                        /\ vote.value = v )
                    \/ (c < Threshold[a])

\*=====================================================================
\*  Actions
\*=====================================================================
PromiseIncrease ==
    \E a \in Acceptor :
        \E b \in Ballot :
            /\ b > Threshold[a]
            /\ UNCHANGED Votes
            /\ Threshold' = [Threshold EXCEPT ![a] = b]

VoteAction ==
    \E a \in Acceptor :
        \E b \in Ballot :
            \E v \in Value :
                /\ b >= Threshold[a]
                /\ \A vote \in Votes[a] : vote.ballot # b
                /\ \A a2 \in Acceptor :
                       \A vote2 \in Votes[a2] :
                           (vote2.ballot = b) => vote2.value = v
                /\ Safe(b, v)
                /\ Votes' = [Votes EXCEPT ![a] = Votes[a] \cup { [ballot |-> b, value |-> v] }]
                /\ Threshold' = [Threshold EXCEPT ![a] = b]

Next == \/ PromiseIncrease
        \/ VoteAction

\*=====================================================================
\*  Specification
\*=====================================================================
Spec == Init /\ [][Next]_<<Votes, Threshold>>

\*=====================================================================
\*  Type and safety invariants
\*=====================================================================
TypeInv ==
    /\ Votes \in [Acceptor -> SUBSET Vote]
    /\ Threshold \in [Acceptor -> Int]

SafeVoteInv ==
    \A a \in Acceptor :
        \A vote \in Votes[a] :
            Safe(vote.ballot, vote.value)

OneValuePerBallot ==
    \A b \in Ballot :
        \A v1, v2 \in Value :
            ( (\E a1 \in Acceptor : \E vote1 \in Votes[a1] :
                    /\ vote1.ballot = b
                    /\ vote1.value = v1) 
              /\ 
              (\E a2 \in Acceptor : \E vote2 \in Votes[a2] :
                    /\ vote2.ballot = b
                    /\ vote2.value = v2) )
            => v1 = v2

Inv == /\ TypeInv
       /\ SafeVoteInv
       /\ OneValuePerBallot

\*=====================================================================
\*  Consensus property
\*=====================================================================
Chosen(b, v) ==
    \E Q \in Quorum :
        \A a \in Q :
            \E vote \in Votes[a] :
                /\ vote.ballot = b
                /\ vote.value = v

ConsensusSpecBar ==
    \A b1, b2 \in Ballot :
        \A v1, v2 \in Value :
            (Chosen(b1, v1) /\ Chosen(b2, v2)) => v1 = v2

\*=====================================================================
\*  Symmetry set (all permutations of Acceptor)
\*=====================================================================
IsBijective(f) ==
    /\ DOMAIN f = Acceptor
    /\ RANGE f = Acceptor
    /\ \A a1, a2 \in Acceptor : f[a1] = f[a2] => a1 = a2

MCSymmetry == { f \in [Acceptor -> Acceptor] : IsBijective(f) }

====