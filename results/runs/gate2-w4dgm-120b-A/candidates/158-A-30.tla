---- MODULE Voting ----
\* A voting-based consensus algorithm: acceptors cast votes in numbered ballots,
\* and a chosen value is backed by a quorum of acceptors all voting for it in the
\* same ballot. Once a value is chosen, no different value can ever be chosen.
EXTENDS Naturals, FiniteSets

CONSTANTS Acceptor, Value, Quorum, Ballot

ASSUME Quorum \subseteq (SUBSET Acceptor) /\ Quorum # {}
ASSUME \A q1 \in Quorum, q2 \in Quorum : q1 \cap q2 # {}

VARIABLES votes, threshold

vars == <<votes, threshold>>

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ threshold \in [Acceptor -> Ballot]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> 0 - 1]

Vote(a, b, v) ==
  /\ b >= threshold[a]
  /\ \A w \in votes[a] : w[1] # b
  /\ \A c \in Acceptor :
       (\A w \in votes[c] : w[1] # b \/ w[2] = v) =>
         (\A q \in Quorum : \A d \in q : \A w \in votes[d] : w[1] = b => w[2] = v)
  /\ \A q \in Quorum : \A c \in q :
       (\A w \in votes[c] : w[1] >= b) =>
         (\A d \in q : \A w \in votes[d] : w[1] >= b => w[2] = v)
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]

Raise(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

Next ==
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)
  \/ \E a \in Acceptor, b \in Ballot : Raise(a, b)

Spec == Init /\ [][Next]_vars

AtMostOneChosen ==
  \A q1 \in Quorum, q2 \in Quorum :
    (\A a \in q1, b \in Ballot : \E v \in Value : <<b, v>> \in votes[a]) =>
      (\A a \in q2, b \in Ballot : \E v \in Value : <<b, v>> \in votes[a])
      => (\A a \in q1 : \A w \in votes[a] : (\E c \in q2, x \in Ballot, y \in Value : <<x, y>> \in votes[c]) => w[2] = y)

Inv == AtMostOneChosen

\* Abstraction: each chosen value is backed by a quorum in some ballot.
ConsensusSpecBar ==
  \A v \in Value :
    (\E a \in Acceptor, b \in Ballot : <<b, v>> \in votes[a])
      => (\E q \in Quorum, b \in Ballot : \A a \in q : <<b, v>> \in votes[a])

\* The constants may be instantiated as finite subsets/intervals for model checking.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot
====