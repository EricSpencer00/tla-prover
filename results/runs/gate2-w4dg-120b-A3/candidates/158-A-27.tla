---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

VARIABLES votes, threshold
vars == <<votes, threshold>>

Quorums == Quorum
Ballots == Ballot

Blank == "blank"

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET (Ballots \X Value)]
  /\ threshold \in [Acceptor -> {-1} \cup Ballots]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

NoVote(a, b) == \A v \in Value : <<b, v>> \notin votes[a]
OtherVoted(b, v) == \E a \in Acceptor : <<b, v>> \in votes[a]
AnotherVoted(b, v) == \E a \in Acceptor, w \in Value : /\ <<b, w>> \in votes[a] /\ w # v

QuorumUnsafe(b, v) ==
  \A q \in Quorums :
    \E a \in q : <<b, v>> \in votes[a]

VoteSafe(b, v) ==
  \A c \in Ballots :
    (c < b) =>
      (\A q \in Quorums :
        \E a \in q : \/ <<c, v>> \in votes[a] \/ (\A x \in Value : NoVote(a, c)))

Promised(a, b) == b >= threshold[a]

Promote(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

Vote(a, b, v) ==
  /\ Promised(a, b)
  /\ NoVote(a, b)
  /\ ~AnotherVoted(b, v)
  /\ QuorumUnsafe(b, v)
  /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballots : Promote(a, b)
  \/ \E a \in Acceptor, b \in Ballots, v \in Value : Vote(a, b, v)

Spec == Init /\ [][Next]_vars

Chosen == {v \in Value : \E q \in Quorums : \A a \in q : \E b \in Ballots : <<b, v>> \in votes[a]}

Inv ==
  /\ \A a \in Acceptor : \A w \in votes[a] : VoteSafe(w[1], w[2])
  /\ \A a, b \in Acceptor : \A v, w \in Value :
       ((<<b, v>> \in votes[a] /\ <<b, w>> \in votes[b]) => v = w)
  /\ TypeOK

ConsensusSpecBar == Cardinality(Chosen) <= 1

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

MCSymmetry == {[x |-> x : x \in Acceptor]}
====