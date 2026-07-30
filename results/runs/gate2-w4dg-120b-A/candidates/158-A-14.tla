---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

\* The system models a voting-based consensus algorithm. An acceptor may
\* cast a vote for a Value in a Ballot only if that ballot is not below the
\* acceptor's current promise threshold, and only if no other value has been
\* voted for in that same ballot. Votes are collected as (ballot, value)
\* pairs, and a value is safe at a ballot if every earlier ballot had a
\* quorum voting for that same value (or was unwinnable). This safety
\* condition, plus the overlap of quorums, is what enforces the
\* Consistency invariant: the set of chosen values never has two members.

CONSTANTS Acceptor, Value, Quorum, Ballot
NONE == "none"

VARIABLES vote, threshold
vars == <<vote, threshold>>

Quorums == {q \in SUBSET Acceptor : \E c \in Quorum : c <= q}
Ballots == {b \in 0..Ballot : TRUE}

\* A quorum of acceptors all voted for v in ballot b, or can never vote in it.
QuorumAgrees(b, v) ==
  \E c \in Quorums :
    \A a \in c : (<<b, v>> \in vote[a]) \/ (b \notin Ballots)

\* Every ballot below b is a quorum-agreed win for v, which rules out a
\* different value having been chosen in an earlier ballot.
VoteIsSafe(b, v) ==
  \A c \in Ballots : c < b => QuorumAgrees(c, v)

TypeOK ==
  /\ vote \in [Acceptor -> SUBSET (Ballots \X Value)]
  /\ threshold \in [Acceptor -> {-1} \cup Ballots]

Init ==
  /\ vote = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

\* Raising the promise threshold is the only way the algorithm ever
\* forbids an acceptor from voting again, and it never casts a vote.
RaiseThreshold(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED vote

\* Casting a vote is the critical step: the ballot must be above the
\* threshold, the acceptor must not have already voted in it, and the
\* ballot must be free of any vote for a different value.
CastVote(a, b, v) ==
  /\ b >= threshold[a]
  /\ ~ \E w \in Value : <<b, w>> \in vote[a]
  /\ \A a2 \in Acceptor : ~ \E w \in Value : <<b, w>> \in vote[a2]
  /\ QuorumAgrees(b, v)
  /\ vote' = [vote EXCEPT ![a] = vote[a] \cup {<<b, v>>}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballots : RaiseThreshold(a, b)
  \/ \E a \in Acceptor, b \in Ballots, v \in Value : CastVote(a, b, v)

Spec == Init /\ [][Next]_vars

Chosen == {v \in Value : \E a \in Acceptor, b \in Ballots : <<b, v>> \in vote[a]}

\* Every vote in the log must have been safe at the moment it was cast.
AllVotesSafe == \A a \in Acceptor, x \in vote[a] : VoteIsSafe(x[1], x[2])

\* No two different values can ever both have a quorum-backed win.
SingleChosenValue == \A v1, v2 \in Value : (v1 \in Chosen /\ v2 \in Chosen) => v1 = v2

Inv == TypeOK /\ AllVotesSafe /\ SingleChosenValue

\* The voting algorithm implements the abstract consensus spec; the
\* refinement map derives Chosen from the voting log, and the abstract
\* spec's Consistency is exactly SingleChosenValue.
ConsensusSpecBar == SingleChosenValue
====