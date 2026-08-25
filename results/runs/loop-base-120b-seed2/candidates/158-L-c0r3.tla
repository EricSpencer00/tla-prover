---- MODULE Voting ----
EXTENDS Naturals, Integers, FiniteSets, Sequences

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

VARIABLES Votes, Threshold

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
IsBijective(f) ==
  /\ \A x, y \in Acceptor : f[x] = f[y] => x = y
  /\ \A a \in Acceptor : \E a0 \in Acceptor : f[a0] = a

\* A vote is a record with fields ballot and value
VoteRecord(b, v) == [ballot |-> b, value |-> v]

\* Safety of a value v at ballot b with respect to a particular quorum Q
SafeAt(v, b, Q) ==
  \A c \in Ballot :
    (c < b) =>
      \A a \in Q :
        ( \E vote \in Votes[a] : vote.ballot = c /\ vote.value = v )
        \/ (Threshold[a] > c)

\* Existence of a quorum that demonstrates safety
Safe(v, b) == \E Q \in Quorum : SafeAt(v, b, Q)

\* A value is chosen if some quorum has all its members voting for it in the same ballot
Chosen(v) ==
  \E b \in Ballot :
    \E Q \in Quorum :
      \A a \in Q :
        \E vote \in Votes[a] : vote.ballot = b /\ vote.value = v

\* Consistency: at most one value can be chosen
Consistent ==
  \A val1, val2 \in Value :
    (Chosen(val1) /\ Chosen(val2)) => val1 = val2

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ Votes = [a \in Acceptor |-> {}]
  /\ Threshold = [a \in Acceptor |-> -1]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Promise increase (no vote)
PromiseIncrease ==
  \E a \in Acceptor, b \in Ballot :
    /\ b > Threshold[a]
    /\ Threshold' = [Threshold EXCEPT ![a] = b]
    /\ UNCHANGED Votes

\* 2. Vote in a ballot
CastVote ==
  \E a \in Acceptor, b \in Ballot, v \in Value :
    /\ b >= Threshold[a]                     \* not below current promise
    /\ ~(\E vote \in Votes[a] : vote.ballot = b)   \* a has not voted in b yet
    /\ \A a_ \in Acceptor :
         \A vote2 \in Votes[a_] :
           (vote2.ballot = b) => (vote2.value = v)   \* no conflicting vote
    /\ Safe(v, b)                               \* safety quorum exists
    /\ Votes' = [Votes EXCEPT ![a] = Votes[a] \cup { VoteRecord(b, v) }]
    /\ Threshold' = [Threshold EXCEPT ![a] = b]
    /\ UNCHANGED << >>

Next ==
  \/ PromiseIncrease
  \/ CastVote

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Votes, Threshold>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
\* Type correctness of Votes and Threshold
TypeCorrect ==
  /\ \A a \in Acceptor : Votes[a] \subseteq [ballot : Ballot, value : Value]
  /\ \A a \in Acceptor : Threshold[a] \in Int

\* Every vote cast is safe at its ballot
AllVotesSafe ==
  \A a \in Acceptor :
    \A vote \in Votes[a] :
      Safe(vote.value, vote.ballot)

\* At most one value per ballot across all acceptors
OneValuePerBallot ==
  \A b \in Ballot :
    \A a1_ , a2_ \in Acceptor :
      \A val1_ , val2_ \in Value :
        (VoteRecord(b, val1_) \in Votes[a1_] /\ VoteRecord(b, val2_) \in Votes[a2_]) => val1_ = val2_

\* Quorum overlap property
QuorumOverlap ==
  \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

Inv == TypeCorrect /\ AllVotesSafe /\ OneValuePerBallot /\ QuorumOverlap

\* ----------------------------------------------------------------------
\* Property to be checked (defined in the generated MCVoting module)
\* ----------------------------------------------------------------------
\* ConsensusSpecBar is provided by the configuration module.

====