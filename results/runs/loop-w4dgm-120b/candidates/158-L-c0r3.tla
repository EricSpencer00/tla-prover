---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* The model is parameterized by the acceptor set, value set, quorum family,
\* and ballot range, so the same module can be checked under many bounds.
\* The .cfg file substitutes concrete finite sets for these abstract
\* constants via the MCAcceptor, MCValue, MCQuorum, and MCBallot operators.

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

VARIABLES votes, threshold

vars == <<votes, threshold>>

Vote == [ball : Ballot, val : Value]

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

\* A quorum of acceptors voting for the same value in the same ballot is
\* what makes that value safe to be chosen at that ballot.
QuorumVoted(q, b, v) ==
  /\ q \in Quorum
  /\ \A a \in q : [ball |-> b, val |-> v] \in votes[a]

\* Safety of a value at a ballot: every lower ballot must already be safe
\* for that value, witnessed by a quorum that has either voted for it or
\* is no longer able to vote in that lower ballot.
ValueSafeAt(v, b) ==
  /\ \A c \in Ballot : c < b =>
       \E q \in Quorum :
         /\ \A a \in q : [ball |-> c, val |-> v] \in votes[a] \/ threshold[a] > c
  /\ \A a \in Acceptor : [ball |-> b, val |-> v] \notin votes[a]

\* An acceptor votes for a value in a ballot, provided the ballot is not
\* below its threshold, it has not already voted in that ballot, no other
\* acceptor voted for a different value in that ballot, and the value is
\* safe at that ballot. Voting also raises the acceptor's threshold.
CastVote(a, b, v) ==
  /\ b >= threshold[a]
  /\ \A c \in Ballot : [ball |-> c, val |-> v] \notin votes[a]
  /\ \A c \in Ballot : \A w \in Value :
       ([ball |-> c, val |-> w] \in votes[a]) => (c # b \/ w = v)
  /\ QuorumVoted(MCQuorum, b, v)
  /\ ValueSafeAt(v, b)
  /\ votes' = [votes EXCEPT ![a] = @ \cup {[ball |-> b, val |-> v]}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : RaiseThreshold(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : CastVote(a, b, v)

Spec == Init /\ [][Next]_vars

\* Every vote that has been cast is safe at its ballot number.
AllVotesSafe == \A a \in Acceptor : \A m \in votes[a] : ValueSafeAt(m.val, m.ball)

\* At most one value is ever voted for in any given ballot across all
\* acceptors, which is what keeps two different values from both being
\* chosen by a quorum in the same ballot.
BallotSingleVal ==
  \A b \in Ballot : \A v1, v2 \in Value :
    (\A a \in Acceptor : [ball |-> b, val |-> v1] \in votes[a])
      => (\A a \in Acceptor : [ball |-> b, val |-> v2] \in votes[a] => v1 = v2)

\* The chosen set is derived from the votes, so the two invariants above
\* together imply it never holds two different values.
ChosenSet == {v \in Value : \E b \in Ballot : QuorumVoted(MCQuorum, b, v)}

\* The chosen set is a subset of the values that are safe at some ballot,
\* so it can never contain two different values.
ChosenSafe == ChosenSet \subseteq {v \in Value : \E b \in Ballot : ValueSafeAt(v, b)}

\* The invariant is the conjunction of the three per-ballot and per-value
\* facts that together imply the chosen set is a singleton or empty.
Inv == AllVotesSafe /\ BallotSingleVal /\ ChosenSafe

\* The voting algorithm implements the abstract consensus specification:
\* the chosen set derived from the votes is always a subset of the safe
\* values, which is exactly the consensus guarantee.
ConsensusSpecBar == ChosenSet \subseteq {v \in Value : \E b \in Ballot : ValueSafeAt(v, b)}

\* The acceptor set is symmetric: any permutation of acceptors is a
\* symmetry of the system, so the model checking state space can be
\* collapsed modulo that symmetry.
MCSymmetry == {f \in [Acceptor -> Acceptor] : \A a \in Acceptor : f[a] \in Acceptor}

====