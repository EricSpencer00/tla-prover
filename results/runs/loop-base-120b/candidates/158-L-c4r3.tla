---- MODULE Voting ----
EXTENDS Naturals, Integers, FiniteSets, TLC

\* ------------------------------------------------------------------------
\* Constants (to be instantiated by the model checker)
\* ------------------------------------------------------------------------
CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* ------------------------------------------------------------------------
\* Substitution operators required by the .cfg file
\* ------------------------------------------------------------------------
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\* ------------------------------------------------------------------------
\* Record representing a single vote
\* ------------------------------------------------------------------------
Vote == [b : Ballot, v : Value]

VARIABLES votes, thresh

\* ------------------------------------------------------------------------
\* Initial state
\* ------------------------------------------------------------------------
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ thresh = [a \in Acceptor |-> -1]

\* ------------------------------------------------------------------------
\* Helper predicates
\* ------------------------------------------------------------------------
AlreadyVotedIn(a, b) ==
    \E w \in votes[a] : w.b = b

NoConflictingVote(b, v) ==
    \A a \in Acceptor: \A w \in votes[a] :
        (w.b = b) => (w.v = v)

\* Safety of a vote at ballot b for value v
Safe(b, v) ==
    \A c \in Ballot :
        (c < b) =>
            \E Q \in Quorum :
                \A a \in Q :
                    (\E w \in votes[a] : w.b = c /\ w.v = v) \/ (thresh[a] > c)

\* ------------------------------------------------------------------------
\* Actions
\* ------------------------------------------------------------------------
Promote(a, b) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ b > thresh[a]                \* raise the promise threshold
    /\ UNCHANGED votes
    /\ thresh' = [thresh EXCEPT ![a] = b]

VoteAction(a, b, v) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ v \in Value
    /\ b >= thresh[a]               \* not below current promise
    /\ ~AlreadyVotedIn(a, b)        \* hasn't voted in this ballot yet
    /\ NoConflictingVote(b, v)      \* no different value already voted in b
    /\ Safe(b, v)                   \* safety condition holds
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [b |-> b, v |-> v] }]
    /\ thresh' = [thresh EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptor: \E b \in Ballot: Promote(a, b)
    \/ \E a \in Acceptor: \E b \in Ballot: \E v \in Value: VoteAction(a, b, v)

\* ------------------------------------------------------------------------
\* Specification
\* ------------------------------------------------------------------------
Spec == Init /\ [][Next]_<<votes, thresh>>

\* ------------------------------------------------------------------------
\* Type correctness (renamed to the identifier expected by the .cfg)
\* ------------------------------------------------------------------------
TypeOK ==
    /\ votes \in [Acceptor -> SUBSET Vote]
    /\ \A a \in Acceptor: \A w \in votes[a] :
          /\ w.b \in Ballot
          /\ w.v \in Value
    /\ thresh \in [Acceptor -> Int]
    /\ \A a \in Acceptor: thresh[a] = -1 \/ thresh[a] \in Ballot

\* ------------------------------------------------------------------------
\* One vote per ballot (the predicate expected by the .cfg as OneVote)
\* ------------------------------------------------------------------------
OneVote ==
    \A b \in Ballot :
        LET vals == { v \in Value :
                        \E a \in Acceptor: \E w \in votes[a] :
                            w.b = b /\ w.v = v }
        IN Cardinality(vals) <= 1

\* ------------------------------------------------------------------------
\* Maximum ballot number promised/used by each acceptor (maxBal)
\* ------------------------------------------------------------------------
maxBal ==
    [a \in Acceptor |-> 
        IF votes[a] = {} 
        THEN -1 
        ELSE Max({ w.b : w \in votes[a] })]

\* ------------------------------------------------------------------------
\* All votes are safe (as required by the invariant AllVotesSafe)
\* ------------------------------------------------------------------------
AllVotesSafe ==
    \A a \in Acceptor: \A w \in votes[a] : Safe(w.b, w.v)

\* ------------------------------------------------------------------------
\* Composite invariant (the identifier required by the .cfg)
\* ------------------------------------------------------------------------
Inv == TypeOK /\ OneVote /\ AllVotesSafe

\* ------------------------------------------------------------------------
\* Consistency property (the identifier required by the .cfg)
\* ------------------------------------------------------------------------
ConsensusSpecBar ==
    \A b1, b2 \in Ballot, val1, val2 \in Value :
        ( \E Q1 \in Quorum :
            \A a \in Q1 :
                \E w \in votes[a] : w.b = b1 /\ w.v = val1 )
        /\ ( \E Q2 \in Quorum :
            \A a \in Q2 :
                \E w \in votes[a] : w.b = b2 /\ w.v = val2 )
        => val1 = val2

\* ------------------------------------------------------------------------
\* Symmetry set required by the .cfg (identity permutation)
\* ------------------------------------------------------------------------
MCSymmetry == { [a \in Acceptor |-> a] }

====