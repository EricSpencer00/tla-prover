---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences

(* ----------------------------------------------------------------------
   Constants (to be instantiated in the .cfg file)
   ---------------------------------------------------------------------- *)
CONSTANTS
    Acceptor,   \* set of acceptor identifiers
    Value,      \* set of possible values
    Quorum,     \* set of quorums, each quorum is a subset of Acceptor
    Ballot      \* set of ballot numbers (natural numbers)

(* ----------------------------------------------------------------------
   Derived constant: the set of all quorum subsets (for convenience)
   ---------------------------------------------------------------------- *)
QUORUMS == Quorum

(* ----------------------------------------------------------------------
   Type definitions
   ---------------------------------------------------------------------- *)
Vote == [ballot : Ballot, val : Value, acc : Acceptor]

(* ----------------------------------------------------------------------
   State variables
   ---------------------------------------------------------------------- *)
VARIABLES
    votes,      \* votes == [a \in Acceptor |-> SUBSET { [b |-> Ballot, v |-> Value] }]
    threshold   \* threshold == [a \in Acceptor |-> Ballot]

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)

(* The set of votes cast by a particular acceptor *)
VotesOf(a) == votes[a]

(* The set of all votes in the system *)
AllVotes == { v \in UNION { votes[a] : a \in Acceptor } : TRUE }

(* The set of quorum subsets *)
AllQuorums == QUORUMS

(* Safety of a value at a given ballot:
   For every lower ballot c, there exists a quorum such that each member
   either has voted for the value at c or cannot vote at c because its
   threshold is already > c. *)
SafeAt(val, b) ==
    \A c \in Ballot :
        c < b =>
            \E q \in AllQuorums :
                \A a \in q :
                    ( \E v \in votes[a] : /\ v.ballot = c /\ v.val = val )
                    \/ threshold[a] > c

(* A quorum that unanimously votes for a value in a ballot *)
QuorumVotes(q, val, b) ==
    \A a \in q : \E v \in votes[a] : /\ v.ballot = b /\ v.val = val

(* Chosen values: there exists a quorum that unanimously voted for the value
   in some ballot *)
Chosen == { val \in Value :
                \E b \in Ballot :
                    \E q \in AllQuorums : QuorumVotes(q, val, b) }

(* ----------------------------------------------------------------------
   Initial predicate
   ---------------------------------------------------------------------- *)
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> -1]

(* ----------------------------------------------------------------------
   Actions
   ---------------------------------------------------------------------- *)

(* 1. Increase promise threshold without voting *)
IncreasePromise ==
    \E a \in Acceptor :
        \E newB \in Ballot :
            /\ newB > threshold[a]
            /\ threshold' = [threshold EXCEPT ![a] = newB]
            /\ UNCHANGED votes

(* 2. Cast a vote for a value in a ballot, respecting all conditions *)
CastVote ==
    \E a \in Acceptor :
      \E b \in Ballot :
        \E v \in Value :
          /\ b >= threshold[a]                         \* not below current promise
          /\ \A vv \in votes[a] : vv.ballot # b        \* hasn't voted in this ballot yet
          /\ \A a2 \in Acceptor :
                \A vv \in votes[a2] :
                    (vv.ballot = b) => (vv.val = v)   \* no other value in same ballot
          /\ SafeAt(v, b)                              \* value is safe at b
          /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b, val |-> v, acc |-> a] }]
          /\ threshold' = [threshold EXCEPT ![a] = b]

Next == IncreasePromise \/ CastVote

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<votes, threshold>>

(* ----------------------------------------------------------------------
   Invariant used for model checking
   ---------------------------------------------------------------------- *)
Inv ==
    /\ \A a \in Acceptor : votes[a] \subseteq { [ballot |-> b, val |-> v, acc |-> a] :
                                               b \in Ballot /\ v \in Value }
    /\ \A a \in Acceptor : threshold[a] \in Ballot \cup {-1}
    /\ \A v \in AllVotes : SafeAt(v.val, v.ballot)

(* ----------------------------------------------------------------------
   Property expressing the consensus guarantee
   ---------------------------------------------------------------------- *)
ConsensusSpecBar ==
    /\ Cardinality(Chosen) <= 1

=============================================================================