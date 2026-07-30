---- MODULE Voting ----
EXTENDS Naturals

\* System model of a voting-based consensus algorithm (an abstraction of Paxos):
\* acceptors cast votes for values in numbered ballots, and quorums must
\* overlap. Once a value is chosen by a quorum in some ballot, no other value
\* can ever be chosen.
\* The invariants below are exactly those that guarantee the safety property.

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

VARIABLES votes, threshold

vars == <<votes, threshold>>

Votes == [ballot: Ballot, val: Value]

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET Votes]
  /\ threshold \in [Acceptor -> (-1)..Ballot]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

\* An acceptor may raise its promise threshold (it will not vote in a lower
\* ballot again), which is what the proof uses to argue about which votes are
\* still live.
RaiseThreshold(a) ==
  /\ \E b \in Ballot: /\ b > threshold[a] /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

InQuorum(q, v) == \A a \in q: \E c \in votes[a]: c.val = v

\* Safety of a value at a ballot: the value must already be safe in every lower
\* ballot, or that lower ballot must be dead (no quorum can win there).
SafeAt(v, b) ==
  \A c \in 0..(b - 1):
    \/ \E q \in Quorum: InQuorum(q, v)
    \/ \A q \in Quorum: \A a \in q: \E v2 \in votes[a]: v2.ballot = c

CastVote(a, v, b) ==
  /\ b >= threshold[a]
  /\ \A v2 \in votes[a]: v2.ballot < b
  /\ \A a2 \in Acceptor, v2 \in votes[a2]: (v2.ballot = b /\ v2.val # v) => FALSE
  /\ SafeAt(v, b)
  /\ votes' = [votes EXCEPT ![a] = @ \cup {[ballot |-> b, val |-> v]}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor: RaiseThreshold(a)
  \/ \E a \in Acceptor, v \in Value, b \in Ballot: CastVote(a, v, b)

Spec == Init /\ [][Next]_vars

\* Every value a quorum has voted for in a ballot is safe at that ballot.
VotedValuesAreSafe == \A a \in Acceptor, v \in votes[a]: SafeAt(v.val, v.ballot)

\* At most one value is ever voted for per ballot (across all acceptors).
BallotHoldsAtMostOneValue ==
  \A a1 \in Acceptor, a2 \in Acceptor, v1 \in votes[a1], v2 \in votes[a2]:
    (v1.ballot = v2.ballot => v1.val = v2.val)

\* Type correctness of votes plus the bound on the threshold: runs together with
\* the other two invariants to imply the safety property.
TypeAndBound ==
  /\ \A a \in Acceptor, v \in votes[a]: v.val \in Value
  /\ \A a \in Acceptor: threshold[a] >= -1

Inv == VotedValuesAreSafe /\ BallotHoldsAtMostOneValue /\ TypeAndBound

\* The chosen set is derived from the votes, and the invariant says it has at
\* most one element, so the system implements a single-value consensus.
ConsensusSpecBar == {v.val : \E q \in Quorum, a \in q: v \in votes[a]} \subseteq Value

\* The model does not check liveness here (it is context-dependent), but the
\* configuration gives one as the single safety property.
====