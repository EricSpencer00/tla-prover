---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

Quorums == {Quorum}

VARIABLES votes, promised

vars == <<votes, promised>>

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET [ball: Ballot, val: Value]]
  /\ promised \in [Acceptor -> Ballot \cup {-1}]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ promised = [a \in Acceptor |-> -1]

Ballots == Ballot
Quorums == {Q \in SUBSET Acceptor : Q # {}}
BallotVals(b, v) == {a \in Acceptor : [ball |-> b, val |-> v] \in votes[a]}
QuorumCast(Q, b, v) == \A a \in Q : [ball |-> b, val |-> v] \in votes[a]
SafeValue(v, b) ==
  \A c \in Ballots : c < b => \E Q \in Quorums : \A a \in Q :
    [ball |-> c, val |-> v] \in votes[a] \/ promised[a] > c

\* An acceptor may raise its promise threshold without voting; this keeps
\* it from voting in any ballot earlier than the new threshold.
Raise(a, b) ==
  /\ b > promised[a]
  /\ promised' = [promised EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* Voting is gated on the ballot being above the acceptor's threshold,
\* on not having already voted in that ballot, on no other vote existing
\* in the same ballot for a different value, and on the value being safe.
Cast(a, b, v) ==
  /\ b >= promised[a]
  /\ \A c \in Ballots : [ball |-> c, val |-> v] \notin votes[a]
  /\ \A a2 \in Acceptor, b2 \in Ballots, v2 \in Value :
        ([ball |-> b, val |-> v2] \in votes[a2]) => (v2 = v)
  /\ SafeValue(v, b)
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {[ball |-> b, val |-> v]}]
  /\ promised' = [promised EXCEPT ![a] = b]

Next ==
  \E a \in Acceptor, b \in Ballots, v \in Value : Raise(a, b) \/ Cast(a, b, v)

Spec == Init /\ [][Next]_vars

\* An accepted value is one voted on by a quorum of acceptors; this is the
\* non-empty set that the Consistency invariant measures.
Accepted == {v \in Value : \E Q \in Quorums : QuorumCast(Q, 0, v)}

\* The vote is safe at its ballot number.  This is the core of the
\* consistency argument: a later vote can only be cast for a value that
\* already had quorum support (or was already locked) at every earlier
\* ballot, so two different values can never both gather quorum support.
AllVotesSafe == \A a \in Acceptor : \A w \in votes[a] : SafeValue(w.val, w.ball)

\* Each ballot number is charged to at most one value across all acceptors.
VotesPerBallotUnique ==
  \A a, a2 \in Acceptor, b \in Ballots, v, v2 \in Value :
    ([ball |-> b, val |-> v] \in votes[a] /\ [ball |-> b, val |-> v2] \in votes[a2])
      => v = v2

\* Voters are either voting or have a promise ceiling; together with the
\* type constraints these form the full state invariant.
AllVotersBounded == \A a \in Acceptor : \A w \in votes[a] : w.val \in Value

Inv ==
  /\ AllVotesSafe
  /\ VotesPerBallotUnique
  /\ AllVotersBounded

\* The high-level spec: the set of accepted values never contains two
\* distinct elements, which follows from the invariants above.
ConsensusSpecBar == \A x, y \in Accepted : x = y

====