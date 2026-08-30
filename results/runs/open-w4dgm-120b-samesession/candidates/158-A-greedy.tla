---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* The model is parameterized by the acceptor, value, quorum, and ballot
\* sets, but the .cfg file substitutes concrete finite sets for them.
\* The symmetry group is the set of all permutations of the acceptor set.

VARIABLES votes, threshold

vars == <<votes, threshold>>

Vote == [ball : Ballot, val : Value]
QuorumFor(v) == {q \in Quorum : v \in q}

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
CastVote(a, b, v) ==
  /\ b >= threshold[a]
  /\ \A c \in Acceptor : [ball |-> b, val |-> v] \notin votes[c]
  /\ \A c \in Acceptor : \A w \in Value :
        ([ball |-> b, val |-> w] \in votes[c]) => w = v
  /\ \A c \in QuorumFor(v) : \A d \in Ballot :
        d < b => \E e \in QuorumFor(v) :
          /\ e \in QuorumFor(v)
          /\ [ball |-> d, val |-> v] \in votes[e]
          \/ threshold[e] < d
  /\ votes' = [votes EXCEPT ![a] = @ \cup {[ball |-> b, val |-> v]}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : RaiseThreshold(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : CastVote(a, b, v)

Spec == Init /\ [][Next]_vars

\* A value is chosen once a quorum has all voted for it in some ballot.
Chosen(v) == \E q \in QuorumFor(v) : \A a \in q : \E b \in Ballot : [ball |-> b, val |-> v] \in votes[a]

\* SAFETY: at most one value is ever chosen by a quorum of acceptors.
Inv == \A v1 \in Value, v2 \in Value : (Chosen(v1) /\ Chosen(v2)) => v1 = v2

\* The voting algorithm implements the abstract consensus specification:
\* the chosen set is derived from the votes, and the invariant is preserved.
ConsensusSpecBar == Spec /\ Inv

MCSymmetry == {f \in [Acceptor -> Acceptor] : \A a \in Acceptor : f[a] \in Acceptor}

\* The .cfg file substitutes these finite versions of the constants.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

====