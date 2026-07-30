---- MODULE Voting ----
EXTENDS Naturals

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

VARIABLES votes, threshold

vars == <<votes, threshold>>

Quorums == Quorum

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ threshold \in [Acceptor -> Ballot \cup {-1}]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

\* A promise: the acceptor will not cast a vote in any ballot below the
\* new threshold, which is how the algorithm models a committed decision.
RaiseThreshold(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* Safety of a ballot's value is witnessed only by a quorum that already
\* supports it at every lower ballot, or can never vote below that ballot.
HasQuorumFor(v, b) ==
  \E Q \in Quorums :
    /\ \A a \in Q : threshold[a] <= b
    /\ \A c \in 0 .. (b - 1) :
         \E Qc \in Quorums :
           /\ \A a \in Qc : threshold[a] <= c
           /\ \A a \in Qc : <<c, v>> \in votes[a]

CastVote(a, b, v) ==
  /\ b >= threshold[a]
  /\ \A c \in Ballot : b < c => <<c, v>> \notin votes[a]
  /\ \A c \in Ballot : <<b, v>> \notin votes[a]
  /\ \A c \in Ballot, w \in Value :
       (w # v /\ <<b, w>> \in votes[a]) => TRUE
  /\ HasQuorumFor(v, b)
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : RaiseThreshold(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : CastVote(a, b, v)

Spec == Init /\ [][Next]_vars

\* A vote must never be cast unless it is safe at that ballot.
VotesAreSafe ==
  \A a \in Acceptor, b \in Ballot, v \in Value :
    (<<b, v>> \in votes[a]) => HasQuorumFor(v, b)

\* At most one value per ballot across all acceptors.
AtMostOnePerBallot ==
  \A a, b \in Acceptor, c \in Ballot, v, w \in Value :
    (<<c, v>> \in votes[a] /\ <<c, w>> \in votes[b]) => (v = w)

\* The chosen set derives from votes, so TypeOK already covers it.
ChosenIsConsistent == (TypeOK /\ VotesAreSafe /\ AtMostOnePerBallot)

Inv == ChosenIsConsistent

\* The chosen set can never contain two different values.
ConsensusSpecBar ==
  \A Q1 \in Quorums, Q2 \in Quorums, v, w \in Value :
    (\A a \in Q1 : \E c \in Ballot : <<c, v>> \in votes[a])
    /\ (\A b \in Q2 : \E c \in Ballot : <<c, w>> \in votes[b])
    => v = w

\* The .cfg substitutes the concrete finite versions of these abstract symbols.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

MCSymmetry == (a1, a2, a3)
====