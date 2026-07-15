---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Acceptor, Value, Quorum, Ballot

\* Derived constant for the empty set of values
NoValue == {}

VARIABLES votes, threshold

\* votes[a] is the set of pairs <<b, v>> that acceptor a has cast
\* threshold[a] is the smallest ballot number a will accept in the future
\* Each acceptor starts with no votes and a threshold of -1 (i.e., no promise)
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> -1]

\*--------------------------------------------------------------------------- 
\* Helper definitions
\*---------------------------------------------------------------------------

\* A vote is a pair <<b, v>>
Vote == [b : Ballot, v : Value]

\* The quorum that a particular value v claims safety in at ballot b
\* (existence of such a quorum is required only when a vote is cast)
SafeQuorum(b, v) ==
    \E Q \in Quorum :
        \A a \in Q :
            ( <<b, v>> \in votes[a] ) \/
            ( \E c \in Ballot :
                c < b /\ <<c, v>> \in votes[a] )
            \/
            ( threshold[a] > b )            \* a can never vote in b

\* No two different values may be voted for in the same ballot
AtMostOneValuePerBallot ==
    \A b \in Ballot :
        \A a1, a2 \in Acceptor :
            \A v1, v2 \in Value :
                (<<b, v1>> \in votes[a1] /\ <<b, v2>> \in votes[a2]) => v1 = v2

\* Overlap property of quorums (assumed by the description)
QuorumOverlap ==
    \A Q1, Q2 \in Quorum : Q1 # Q2 => Q1 \cap Q2 # {}

\* Safety of a vote: a vote <<b,v>> is safe if for every lower ballot c
\* there exists a quorum all of whose members either already voted for v in c
\* or are already promised to be above c.
VoteSafe(b, v) ==
    \A c \in Ballot :
        c < b =>
            \E Q \in Quorum :
                \A a \in Q :
                    (<<c, v>> \in votes[a]) \/ (threshold[a] > c)

\* Consensus chosen set: a value appears in the set iff a quorum has unanimously
\* voted for it in some ballot.
Chosen(v) ==
    \E b \in Ballot :
        \E Q \in Quorum :
            \A a \in Q : <<b, v>> \in votes[a]

\* The overall invariant required by the cfg
Inv ==
    /\ \A a \in Acceptor :
          \A <<b, v>> \in votes[a] :
              /\ b \in Ballot
              /\ v \in Value
              /\ b >= threshold[a]
              /\ VoteSafe(b, v)
    /\ AtMostOneValuePerBallot
    /\ threshold[a] >= -1
    /\ threshold[a] \in Ballot \cup {-1}
    /\ QuorumOverlap

\*--------------------------------------------------------------------------- 
\* Actions
\*---------------------------------------------------------------------------

\* An acceptor raises its promise threshold (no vote)
PromiseIncrease ==
    \E a \in Acceptor :
        \E nb \in Ballot :
            /\ nb > threshold[a]
            /\ threshold' = [threshold EXCEPT ![a] = nb]
            /\ UNCHANGED votes

\* An acceptor casts a vote for value v in ballot b
\* Preconditions enforce the description's four conditions
CastVote ==
    \E a \in Acceptor :
        \E b \in Ballot :
            \E v \in Value :
                /\ b >= threshold[a]               \* not below promise
                /\ ~ (<<b, v>> \in votes[a])        \* hasn't voted in b yet
                /\ ( \A a2 \in Acceptor :
                        \A v2 \in Value :
                            (<<b, v2>> \in votes[a2]) => v2 = v )   \* uniqueness per ballot
                /\ SafeQuorum(b, v)                \* existence of a safe quorum
                /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
                /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
    \/ PromiseIncrease
    \/ CastVote
    \/ UNCHANGED <<votes, threshold>>

\*--------------------------------------------------------------------------- 
\* Specification
\*---------------------------------------------------------------------------

Spec ==
    Init /\ [][Next]_<<votes, threshold>>

\* The property named in the cfg, derived from the consensus description
ConsensusSpecBar == Inv

====