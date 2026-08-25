---- MODULE Voting ----
EXTENDS Naturals, Integers, FiniteSets, Sequences

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES votes, threshold

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* A vote is a record with fields ballot and value
Vote == [ballot : Ballot, value : Value]

\* The set of all votes cast by an acceptor
VotesOf(a) == votes[a]

\* SafeAt(v,b) expresses that value v is safe at ballot b
SafeAt(v, b) ==
  \A c \in Ballot :
    (c < b) => 
      \E Q \in Quorum :
        \A a \in Q :
          ( (\E vv \in votes[a] : vv.ballot = c /\ vv.value = v) 
            \/ threshold[a] > c )

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Promise: raise the promise threshold of an acceptor
Promise ==
  \E a \in Acceptor, b \in Ballot :
    /\ b > threshold[a]
    /\ UNCHANGED votes
    /\ threshold' = [threshold EXCEPT ![a] = b]

\* 2. Vote: an acceptor votes for a value in a ballot
VoteAction ==
  \E a \in Acceptor, b \in Ballot, v \in Value :
    /\ b >= threshold[a]                                   \* not below promise
    /\ ~(\E vv \in votes[a] : vv.ballot = b)               \* hasn't voted in b yet
    /\ \A a2 \in Acceptor :
         (a2 # a) => 
           \A vv2 \in votes[a2] :
             (vv2.ballot = b) => vv2.value = v            \* no conflicting vote
    /\ SafeAt(v, b)                                        \* value is safe
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b, value |-> v] }]
    /\ threshold' = [threshold EXCEPT ![a] = b]

Next == \/ Promise \/ VoteAction

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<votes, threshold>>

\* ----------------------------------------------------------------------
\* Invariant
\* ----------------------------------------------------------------------
\* (a) Every vote is safe at its ballot
AllVotesSafe ==
  \A a \in Acceptor :
    \A vv \in votes[a] : SafeAt(vv.value, vv.ballot)

\* (b) At most one value per ballot across all acceptors
AtMostOneValuePerBallot ==
  \A b \in Ballot :
    \A v1, v2 \in Value :
      ( (\E a1 \in Acceptor : \E vv1 \in votes[a1] : vv1.ballot = b /\ vv1.value = v1) 
        /\ (\E a2 \in Acceptor : \E vv2 \in votes[a2] : vv2.ballot = b /\ vv2.value = v2) )
      => v1 = v2

\* (c) Type correctness (implicit in Init/Next, but stated explicitly)
TypesOk ==
  /\ votes \in [Acceptor -> SUBSET Vote]
  /\ threshold \in [Acceptor -> Int]

Inv == AllVotesSafe /\ AtMostOneValuePerBallot /\ TypesOk

\* ----------------------------------------------------------------------
\* Property: Consensus (at most one chosen value)
\* ----------------------------------------------------------------------
Chosen ==
  { v \in Value :
      \E b \in Ballot, Q \in Quorum :
        \A a \in Q :
          \E vv \in votes[a] : vv.ballot = b /\ vv.value = v }

ConsensusSpecBar == 
  \A v1, v2 \in Value :
    (v1 \in Chosen /\ v2 \in Chosen) => v1 = v2

\* ----------------------------------------------------------------------
\* Symmetry definition (identity permutation)
\* ----------------------------------------------------------------------
IdentityPerm == [a \in Acceptor |-> a]

MCSymmetry == { IdentityPerm }

\* ----------------------------------------------------------------------
\* Operators for model checking substitution
\* ----------------------------------------------------------------------
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

====