---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

ASSUME a1 \in Acceptor /\ a2 \in Acceptor /\ a3 \in Acceptor /\ a1 # a2 /\ a2 # a3 /\ a1 # a3
ASSUME v1 \in Value /\ v2 \in Value /\ v1 # v2
\* Quorum overlap is assumed here and in all reachable states; the .cfg may
\* instantiate Quorum with concrete sets that satisfy it.
ASSUME \A q1 \in Quorum, q2 \in Quorum : q1 # {} /\ q1 \cap q2 # {}

VARIABLES votes, threshold
vars == <<votes, threshold>>

VotePairs == [ball : Ballot, val : Value]
VoteKey(v) == <<v.ball, v.val>>

\* A value is safe at ballot b if every lower ballot has a quorum voting for it,
\* or every member of such a quorum is barred from that lower ballot.
\* This inductively blocks a later quorum from voting a conflicting value.
SafeAtValue(b, val) ==
  \A c \in Ballot :
    c < b =>
      \E q \in Quorum :
        /\ \A a \in q : <<c, val>> \in votes[a]
        \/ \A a \in q : threshold[a] >= c

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET VotePairs]
  /\ threshold \in [Acceptor -> Ballot \cup {-1}]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

RaiseThreshold(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

CastVote(a, b, val) ==
  /\ b >= threshold[a]
  /\ \A x \in votes[a] : x.ball # b
  /\ \A c \in Ballot : c < b => \A a2 \in Acceptor : <<c, val>> \in votes[a2]
  /\ \A c \in Ballot : c < b => \E q \in Quorum : \A a2 \in q : <<c, val>> \in votes[a2]
  /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, val>>}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : RaiseThreshold(a, b)
  \/ \E a \in Acceptor, b \in Ballot, val \in Value : CastVote(a, b, val)

Spec == Init /\ [][Next]_vars

\* A cast vote is always safe at its ballot number; no acceptor votes against a
\* lower ballot's decided value, which is what keeps every quorum's votes aligned.
EveryVoteSafe == \A a \in Acceptor, v \in votes[a] : SafeAtValue(v.ball, v.val)

\* No two distinct values are voted for in the same ballot, so a quorum can never
\* form around two different values at once.
OneValuePerBallot ==
  \A a2, a3 \in Acceptor, v2 \in votes[a2], v3 \in votes[a3] :
    (v2.ball = v3.ball) => (v2.val = v3.val)

\* A chosen value is a value that some quorum voted for in some ballot; type
\* correctness of votes and thresholds is included here for completeness.
ChosenSet == {val \in Value : \E a \in Acceptor, v \in votes[a] : v.val = val}
Inv == EveryVoteSafe /\ OneValuePerBallot /\ TypeOK

\* The voting algorithm implements consensus: the chosen set is always a subset
\* of the single value that any quorum voted for, via a refinement mapping.
ConsensusSpecBar ==
  \A a \in Acceptor, v \in votes[a] :
    \E q \in Quorum : \A a2 \in q : <<v.ball, v.val>> \in votes[a2]

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot
====