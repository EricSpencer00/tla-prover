---- MODULE Voting ----
\* ----------------------------------------------------------------------
\* High-level voting-based consensus algorithm (Paxos abstraction)
\* ----------------------------------------------------------------------
EXTENDS Naturals, FiniteSets

\* ----------------------------------------------------------------------
\* CONSTANTS (provided by the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS a1, Acceptor, Value, Quorum, Ballot

\* ----------------------------------------------------------------------
\* Type definitions (for readability, not part of required identifiers)
\* ----------------------------------------------------------------------
\* Vote is a pair <b, v> where b \in Ballot and v \in Value
Vote == [b: Ballot, v: Value]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    Votes,   \* Indexed by acceptor:  Votes[a] is a set of Vote pairs
    Threshold \* Indexed by acceptor:  Threshold[a] is the current promise

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Ballot number comparison
GreaterOrEqual(b1, b2) == b1 >= b2

\* Quorum membership
InQuorum(a, Q) == a \in Q

\* SafeAt(b, v): true iff for every lower ballot c < b,
\*                there exists a quorum Q such that for all a \in Q,
\*                a has voted for v in ballot c or can never vote in c.
SafeAt(b, v) ==
    \A c \in 0..(b - 1) :
        \E Q \in Quorum :
            \A a \in Q :
                \E vote \in Votes[a] :
                    (vote.b = c /\ vote.v = v)

\* Quorum overlap assumption (provided externally)
\* This is a property rather than a variable; we state it for the proof.
QuorumOverlap ==
    \A Q1, Q2 \in Quorum :
        Q1 \cap Q2 # {}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Votes = [a \in Acceptor |-> {}]
    /\ Threshold = [a \in Acceptor |-> -1]

\* ----------------------------------------------------------------------
\* Action: Increase promise threshold
\* ----------------------------------------------------------------------
Promise(a, b) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ b > Threshold[a]
    /\ Threshold' = [Threshold EXCEPT ![a] = b]
    /\ Votes' = Votes

\* ----------------------------------------------------------------------
\* Action: Cast a vote for value v in ballot b
\* ----------------------------------------------------------------------
VoteFor(a, b, v) ==
    /\ a \in Acceptor
    /\ v \in Value
    /\ b \in Ballot
    /\ b >= Threshold[a]
    /\ \A vote \in Votes[a] : vote.b # b \* no prior vote in this ballot
    /\ \A a2 \in Acceptor :
          \A vote2 \in Votes[a2] :
              (vote2.b = b => vote2.v = v)      \* no conflicting vote in same ballot
    /\ \E Q \in Quorum :
          \A a3 \in Q :
              \E vote3 \in Votes[a3] :
                  (vote3.b = b /\ vote3.v = v) \* quorum witnesses this vote
    /\ Threshold' = [Threshold EXCEPT ![a] = b]
    /\ Votes' = [Votes EXCEPT ![a] = Votes[a] \cup { [b |-> b, v |-> v] }]

\* ----------------------------------------------------------------------
\* Next-state relation (universal nondeterministic choice)
\* ----------------------------------------------------------------------
Next ==
    \E a \in Acceptor, b \in Ballot :
        Promise(a, b)
    \/ \E a \in Acceptor, b \in Ballot, v \in Value :
        VoteFor(a, b, v)

\* ----------------------------------------------------------------------
\* Specification (required identifier)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Votes, Threshold>>

\* ----------------------------------------------------------------------
\* Safety invariants (required identifier)
\* ----------------------------------------------------------------------
\* (a) Every vote cast is safe
InvSafeVotes ==
    \A a \in Acceptor :
        \A vote \in Votes[a] :
            SafeAt(vote.b, vote.v)

\* (b) At most one value per ballot across all acceptors
InvUniquePerBallot ==
    \A b \in Ballot :
        \E v \in Value :
            ( \A a \in Acceptor :
                \A vote \in Votes[a] :
                    (vote.b = b => vote.v = v) )

\* (c) Type correctness of variables is implied by definitions

Inv == InvSafeVotes /\ InvUniquePerBallot

\* ----------------------------------------------------------------------
\* High-level liveness property (not specified, placeholder)
\* ----------------------------------------------------------------------
\* (No liveness properties required by the configuration)

\* ----------------------------------------------------------------------
\* Abstract consensus property from the .cfg (required identifier)
\* ----------------------------------------------------------------------
ConsensusSpecBar ==
    \A b1, b2 \in Ballot :
        \A v1, v2 \in Value :
            ( \A a \in Acceptor :
                \A vote \in Votes[a] :
                    (vote.b = b1 => vote.v = v1) ->
              \A a \in Acceptor :
                \A vote \in Votes[a] :
                    (vote.b = b2 => vote.v = v2) ->
                v1 = v2)

\* ----------------------------------------------------------------------
\* The module ends here
\* ----------------------------------------------------------------------
====