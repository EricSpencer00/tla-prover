---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS 
    a1, a2, a3,
    v1, v2,
    Acceptor, Value, Quorum, Ballot

\* Substitution operators for the model checker
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

VARIABLES votes, promise

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
VoteRecord == [ballot : Ballot, value : Value]

\* A value v is safe at ballot b if for every lower ballot c there exists a
\* quorum Q such that each member of Q either has already voted for v at c
\* or has promised to only vote in ballots greater than c.
Safe(v, b) ==
    \A c \in Ballot :
        (c < b) => 
            \E Q \in Quorum :
                \A a \in Q :
                    ( \E vr \in votes[a] : vr.ballot = c /\ vr.value = v )
                    \/ (promise[a] > c)

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ promise = [a \in Acceptor |-> -1]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
PromiseIncrease ==
    \E a \in Acceptor, b \in Ballot :
        /\ b > promise[a]                     \* strictly higher
        /\ promise' = [promise EXCEPT ![a] = b]
        /\ UNCHANGED votes

VoteAction ==
    \E a \in Acceptor, b \in Ballot, v \in Value :
        /\ b >= promise[a]                                   \* not below threshold
        /\ ~\E vr \in votes[a] : vr.ballot = b               \* not voted in b yet
        /\ \A a2 \in Acceptor :
              (\E vr2 \in votes[a2] : vr2.ballot = b) =>
                 (\E vr2 \in votes[a2] : vr2.ballot = b /\ vr2.value = v)
        /\ Safe(v, b)                                         \* value is safe
        /\ promise' = [promise EXCEPT ![a] = b]
        /\ votes'   = [votes EXCEPT ![a] = votes[a] \cup
                     { [ballot |-> b, value |-> v] }]

Next == PromiseIncrease \/ VoteAction

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<|votes, promise|>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ votes \in [Acceptor -> SUBSET VoteRecord]
    /\ promise \in [Acceptor -> Int]

OneValuePerBallot ==
    \A b \in Ballot :
        ( \E v \in Value, a \in Acceptor, vr \in votes[a] :
              vr.ballot = b /\ vr.value = v )
        =>
        \A a2 \in Acceptor, vr2 \in votes[a2] :
            vr2.ballot = b => vr2.value = v

AllVotesSafe ==
    \A a \in Acceptor :
        \A vr \in votes[a] : Safe(vr.value, vr.ballot)

Inv == TypeInvariant /\ OneValuePerBallot /\ AllVotesSafe

\* ----------------------------------------------------------------------
\* Safety property: at most one value can be chosen
\* ----------------------------------------------------------------------
ChosenVals ==
    { v \in Value :
        \E b \in Ballot, Q \in Quorum :
            \A a \in Q :
                \E vr \in votes[a] : vr.ballot = b /\ vr.value = v }

ConsensusSpecBar == 
    \A v1, v2 \in Value :
        (v1 \in ChosenVals /\ v2 \in ChosenVals) => v1 = v2

\* ----------------------------------------------------------------------
\* Symmetry definition (permutations of acceptors)
\* ----------------------------------------------------------------------
IsPermutation(p) ==
    /\ DOMAIN p = Acceptor
    /\ RANGE p = Acceptor
    /\ \A a1, a2 \in Acceptor : p[a1] = p[a2] => a1 = a2

MCSymmetry == { p \in [Acceptor -> Acceptor] : IsPermutation(p) }

====