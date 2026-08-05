---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

MCAcceptor == {a1, a2, a3}
MCValue == {v1, v2}
MCQuorum == {q1, q2}
MCBallot == {0, 1}

VARIABLES votes, threshold

vars == <<votes, threshold>>

Vote == [ball : Ballot, val : Value]
QuorumVote == [quorum : Quorum, val : Value]

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET Vote]
  /\ threshold \in [Acceptor -> Ballot \cup {-1}]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

\* An acceptor may raise its promise threshold to a higher ballot number,
\* which prevents it from voting in any ballot below that threshold.
RaiseThreshold(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* An acceptor votes for a value in a ballot, provided the ballot is not
\* below its threshold, it has not already voted in that ballot, no other
\* acceptor voted for a different value in that ballot, and a quorum shows
\* the value is safe at that ballot number.
VoteFor(a, b, v) ==
  /\ b >= threshold[a]
  /\ \A c \in Ballot : [ball |-> c, val |-> v] \notin votes[a]
  /\ \A c \in Acceptor : [ball |-> b, val |-> v] \in votes[c]
       \/ \A c \in Acceptor : [ball |-> b, val |-> v] \notin votes[c]
  /\ \E q \in Quorum :
       \A c \in q :
         (\A d \in Ballot : d < b => [ball |-> d, val |-> v] \in votes[c])
         \/ \A d \in Ballot : d < b => [ball |-> d, val |-> v] \notin votes[c]
  /\ votes' = [votes EXCEPT ![a] = @ \cup {[ball |-> b, val |-> v]}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : RaiseThreshold(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : VoteFor(a, b, v)

Spec == Init /\ [][Next]_vars

\* Every cast vote is safe at its ballot number.
AllVotesSafe ==
  \A a \in Acceptor : \A c \in votes[a] :
    \A d \in Ballot : d < c.ball =>
      \E q \in Quorum : \A e \in q :
        ([ball |-> d, val |-> c.val] \in votes[e] \/ [ball |-> d, val |-> c.val] \notin votes[e])

\* At most one value is voted for per ballot across all acceptors.
AtMostOnePerBallot ==
  \A a, b \in Acceptor : \A c, d \in votes[a] : \A e, f \in votes[b] :
    (c.ball = e.ball /\ c.val # e.val) => (a = b /\ c = e)

\* Type-correctness of votes and thresholds.
TypeOKInv == TypeOK

Inv == AllVotesSafe /\ AtMostOnePerBallot /\ TypeOKInv

\* The chosen set contains at most one value: if a quorum of acceptors has
\* all voted for one value in some ballot, and a quorum has all voted for
\* another value in some ballot, those values must be the same.
ConsensusSpecBar ==
  \A q1, q2 \in Quorum : \A v1, v2 \in Value :
    (\A a \in q1 : [ball |-> 0, val |-> v1] \in votes[a])
      /\ (\A a \in q2 : [ball |-> 0, val |-> v2] \in votes[a])
        => v1 = v2

\* Quorums overlap: any two quorums share at least one acceptor.
QuorumOverlap ==
  \A q1, q2 \in Quorum : q1 # q2 => q1 \cap q2 # {}

====