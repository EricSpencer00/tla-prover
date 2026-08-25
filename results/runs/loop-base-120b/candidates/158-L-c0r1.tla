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
    /\ \A a2_ \in Acceptor :
         (a2_ # a) => 
           \A vv2 \in votes[a2_] :
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
    \A val1, val2 \in Value :
      ( (\E acc1 \in Acceptor : \E vv1 \in votes[acc1] : vv1.ballot = b /\ vv1.value = val1) 
        /\ (\E acc2 \in Acceptor : \E vv2 \in votes[acc2] : vv2.ballot = b /\ vv2.value = val2) )
      => val1 = val2

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
  \A val1, val2 \in Value :
    (val1 \in Chosen /\ val2 \in Chosen) => val1 = val2

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