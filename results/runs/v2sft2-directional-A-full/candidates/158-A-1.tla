---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

(* ----------------------------------------------------------------------
   State variables
   ---------------------------------------------------------------------- *)

VARIABLES votes, threshold

(* ----------------------------------------------------------------------
   Types and helper definitions
   ---------------------------------------------------------------------- *)

\* A vote is a pair <b, v> where b is a ballot and v is a value
Vote == [ballot: Ballot, value: Value]

\* A set of votes cast by an acceptor
AcceptorVotes == [a \in Acceptor |-> SUBSET
                   [b \in Ballot |-> Value]]

\* The threshold for an acceptor (minimum ballot number it will consider)
Thresholds == [a \in Acceptor |-> Nat]

\* The set of all quorums (each quorum is a subset of acceptors)
QuorumSet == Quorum

\* Helper: safe at ballot b for value v
SafeAt(b, v) ==
    \A c \in 0..(b-1) :
        \E q \in QuorumSet :
            \A a \in q :
                (a \in votes => (b \in AcceptorVotes[a] => AcceptorVotes[a][b] = v))
                \/ (a \notin votes)

\* Helper: all votes for a ballot are safe
AllVotesSafe(b) ==
    \A a \in Acceptor :
        \A v \in Value :
            (\E c \in Ballot : c = b /\ v \in AcceptorVotes[a] => SafeAt(b, v))

\* Helper: at most one value voted in a ballot
AtMostOneValuePerBallot(b) ==
    \A v1, v2 \in Value :
        (v1 # v2) => (\E a \in Acceptor : b \in AcceptorVotes[a] /\ AcceptorVotes[a][b] = v1) => (\NOT \E a \in Acceptor : b \in AcceptorVotes[a] /\ AcceptorVotes[a][b] = v2)

\* Helper: type correctness
TypeOK ==
    votes \in AcceptorVotes /\ threshold \in Thresholds

\* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)

Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> -1]

\* ----------------------------------------------------------------------
   Actions
   ---------------------------------------------------------------------- *)

AdvanceThreshold(a, nb) ==
    /\ a \in Acceptor
    /\ nb \in Ballot
    /\ nb > threshold[a]
    /\ threshold' = [threshold EXCEPT ![a] = nb]
    /\ UNCHANGED votes

CastVote(a, b, v) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ v \in Value
    /\ b >= threshold[a]
    /\ b \notin votes[a]
    /\ (\NOT \E a2 \in Acceptor : b \in votes[a2] /\ votes[a2][b] # v)
    /\ (\Exists q \in QuorumSet :
            \A a2 \in q :
                (a2 \in votes => (b \in votes[a2] => votes[a2][b] = v))
                \/ (a2 \notin votes))
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {b -> v}]
    /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
    \/ \E a, nb \in {a1} : AdvanceThreshold(a, nb)
    \/ \E a, b \in {a1} : b \in Ballot : \E v \in Value : CastVote(a, b, v)

Spec ==
    Init /\ [][Next]_<<votes, threshold>>

\* ----------------------------------------------------------------------
   Invariant
   ---------------------------------------------------------------------- *)

Inv ==
    /\ TypeOK
    /\ \A b \in Ballot : AllVotesSafe(b)
    /\ \A b \in Ballot : AtMostOneValuePerBallot(b)

\* ----------------------------------------------------------------------
   Properties
   ---------------------------------------------------------------------- *)

ConsensusSpecBar ==
    INV CoveredBy(Inv)

====