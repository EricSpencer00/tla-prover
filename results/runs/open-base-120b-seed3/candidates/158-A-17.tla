---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* Constants (instantiated by the .cfg file)
\* ----------------------------------------------------------------------
CONSTANT a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* ----------------------------------------------------------------------
\* Operators required by the configuration (aliases for the constants)
\* ----------------------------------------------------------------------
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES Votes, Threshold

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Vote == [ballot : Ballot, value : Value]

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init ==
    /\ Votes = [a \in Acceptor |-> {}]
    /\ Threshold = [a \in Acceptor |-> -1]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Has a given acceptor already voted in ballot b?
HasVoted(a, b) == 
    \E v \in Value : [ballot |-> b, value |-> v] \in Votes[a]

\* Value voted by acceptor a in ballot b (if any)
VotedValue(a, b) == 
    CHOOSE v \in Value : [ballot |-> b, value |-> v] \in Votes[a]

\* Safety of a value at a given ballot
SafeAt(v, b) ==
    \A c \in Ballot :
        (c < b) =>
            \E Q \in Quorum :
                \A a \in Q :
                    ( (\E w \in Value :
                           [ballot |-> c, value |-> w] \in Votes[a] /\ w = v) )
                    \/ (Threshold[a] > c)

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Promise increase (no vote)
PromiseIncrease ==
    \E a \in Acceptor, b \in Ballot :
        /\ b > Threshold[a]
        /\ UNCHANGED Votes
        /\ Threshold' = [Threshold EXCEPT ![a] = b]

\* 2. Vote action
VoteAction ==
    \E a \in Acceptor, b \in Ballot, v \in Value :
        /\ b >= Threshold[a]                     \* not below promise
        /\ ~HasVoted(a, b)                       \* hasn't voted in this ballot yet
        /\ \A a2 \in Acceptor :
               (HasVoted(a2, b) => VotedValue(a2, b) = v)   \* no conflicting vote
        /\ SafeAt(v, b)                          \* safety condition
        /\ Votes' = [Votes EXCEPT ![a] = Votes[a] \cup {[ballot |-> b, value |-> v]}]
        /\ Threshold' = [Threshold EXCEPT ![a] = b]

Next ==
    \/ PromiseIncrease
    \/ VoteAction

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Votes, Threshold>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
\* Type correctness
TypeInv ==
    /\ \A a \in Acceptor : Votes[a] \subseteq Vote
    /\ \A a \in Acceptor : Threshold[a] \in Int

\* At most one value per ballot across all acceptors
SingleValuePerBallot ==
    \A b \in Ballot :
        \A a1, a2 \in Acceptor :
            \A v1, v2 \in Value :
                ( [ballot |-> b, value |-> v1] \in Votes[a1] /\
                  [ballot |-> b, value |-> v2] \in Votes[a2] ) => v1 = v2

\* Every recorded vote is safe at its ballot
VoteSafe ==
    \A a \in Acceptor :
        \A vote \in Votes[a] :
            SafeAt(vote.value, vote.ballot)

Inv == TypeInv /\ SingleValuePerBallot /\ VoteSafe

\* ----------------------------------------------------------------------
\* Chosen definition and consensus property
\* ----------------------------------------------------------------------
Chosen(v, b) ==
    \E Q \in Quorum :
        \A a \in Q :
            \E vote \in Votes[a] :
                vote.ballot = b /\ vote.value = v

ConsensusSpecBar ==
    \A v1, v2 \in Value, b1, b2 \in Ballot :
        (Chosen(v1, b1) /\ Chosen(v2, b2)) => v1 = v2

\* ----------------------------------------------------------------------
\* Symmetry definition (identity permutation)
\* ----------------------------------------------------------------------
MCSymmetry == { [a \in Acceptor |-> a] }

=============================================================================