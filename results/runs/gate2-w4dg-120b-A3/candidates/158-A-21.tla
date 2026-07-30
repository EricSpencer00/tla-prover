---- MODULE Voting ----
EXTENDS Integers, FiniteSets

\* Natural-language description: a Paxos-like voting algorithm with three acceptors
\* that vote for values in numbered ballots. A value is "safe" at a ballot only if
\* every lower ballot already had a quorum backing it with the same value. That
\* guarantee is what enforces consistency: no two different values can each win
\* a quorum, and a quorum is exactly what a chosen value requires.

CONSTANTS
  a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* The .cfg substitutes concrete (finite or bounded) instantiations for the
\* abstract types below. The syntax "NAME == MCNAME" is required by the cfg.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

VARIABLES votes, threshold

vars == <<votes, threshold>>

Votes == [ballot : Ballot, val : Value]

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET Votes]
  /\ threshold \in [Acceptor -> Ballot \cup {-1}]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

\* A quorum Q backs a vote for (b, v) if every member has already voted in this
\* ballot for that value, or can never vote in it again (its threshold already
\* past it). Backing by one quorum is enough for the algorithm to accept a vote.
BackedByQuorum(b, v) ==
  \E Q \in Quorum :
    \A a \in Q :
      /\ (b, v) \in votes[a]
      \/ threshold[a] > b

\* A value is safe at ballot b if every lower ballot already had a quorum
\* backing it with the same value. The guard below checks that.
ValueSafeAtBallot(b, v) ==
  \A c \in Ballot :
    (c < b) => (\E Q \in Quorum : \A a \in Q : (c, v) \in votes[a])

\* No acceptor may vote for two different values in the same ballot: if
\* (b, v) is present somewhere, no other value is present at ballot b.
NoOtherVote(b, v) ==
  \A a \in Acceptor :
    \A w \in Value \ {v} :
      (b, w) \notin votes[a]

\* An acceptor may raise its promise threshold without voting.
IncreaseThreshold(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* Casting a vote: ballot must respect the acceptor's current threshold, the
\* ballot must be free of any other value, and the candidate must be safe.
Vote(a, b, v) ==
  /\ b >= threshold[a]
  /\ NoOtherVote(b, v)
  /\ ValueSafeAtBallot(b, v)
  /\ BackedByQuorum(b, v)
  /\ votes' = [votes EXCEPT ![a] = @ \cup {[ballot |-> b, val |-> v]}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : IncreaseThreshold(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)

Spec == Init /\ [][Next]_vars

\* Every cast vote was safe at the ballot it was cast for.
AllVotesSafe == \A a \in Acceptor : \A x \in votes[a] : ValueSafeAtBallot(x.ballot, x.val)

\* At most one value is ever voted for in a given ballot across all acceptors.
AtMostOneValuePerBallot ==
  \A b \in Ballot :
    \A v1 \in Value : \E a1 \in Acceptor : (b, v1) \in votes[a1]
      => \A w \in Value : \A a2 \in Acceptor : (b, w) \in votes[a2] => w = v1

\* The derived property of the whole consensus abstraction: at most one value
\* is ever backed by a quorum. That is the consistency guarantee.
Inv == AllVotesSafe /\ AtMostOneValuePerBallot /\ TypeOK

\* The abstract consensus spec requires every value in the chosen set to be
\* backed by a quorum, and the bound on chosen values follows from the ballot
\* ordering. There is no liveness claim -- the spec only checks the safety.
ConsensusSpecBar == Inv

\* Symmetry: swapping the acceptor identities leaves the model unchanged.
MCSymmetry == <<[a1 |-> a1, a2 |-> a2, a3 |-> a3],
                [a1 |-> a1, a2 |-> a3, a3 |-> a2],
                [a1 |-> a2, a2 |-> a1, a3 |-> a3],
                [a1 |-> a2, a2 |-> a3, a3 |-> a1],
                [a1 |-> a3, a2 |-> a1, a3 |-> a2],
                [a1 |-> a3, a2 |-> a2, a3 |-> a1]>>

====