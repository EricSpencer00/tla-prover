---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, TLC, SubsetAlgebra

CONSTANTS Acceptor, Value, Quorum, Ballot

VARIABLES votes, minBallot

vars == <<votes, minBallot>>

Vote == [b: Ballot, v: Value]
CastFor(b, v) == { a \in Acceptor : Vote(b, v) \in votes[a] }

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ minBallot = [a \in Acceptor |-> -1]

Accepts(a, b, v) ==
  /\ b >= minBallot[a]
  /\ \A c \in votes[a] : c.b # b
  /\ \A c \in Acceptor : ~(\E w \in Value : w # v /\ Vote(b, w) \in votes[c])
  /\ \E Q \in Quorum : \A x \in Q :
       \E c \in votes[x] : c.b = b /\ c.v = v
       \/ minBallot[x] > b
  /\ votes' = [votes EXCEPT ![a] = @ \cup {Vote(b, v)}]
  /\ minBallot' = [minBallot EXCEPT ![a] = b]

Promise(a, b) ==
  /\ b >= minBallot[a]
  /\ minBallot' = [minBallot EXCEPT ![a] = b]
  /\ UNCHANGED votes

QuietlyPromise ==
  /\ (\E a \in Acceptor, b \in Ballot : Promise(a, b))
  /\ UNCHANGED votes

VoteStep == (\E a \in Acceptor, b \in Ballot, v \in Value: Accepts(a, b, v))

Next == QuietlyPromise \/ VoteStep

Spec == Init /\ [][Next]_vars

QuorumsOverlap == \A Q1 \in Quorum, Q2 \in Quorum : Q1 # Q2 => Q1 \cap Q2 # {}
BallotNumbersAreNaturals == \A b \in Ballot : b \in Nat

Inv ==
  /\ BallotNumbersAreNaturals
  /\ QuorumsOverlap
  /\ \A a \in Acceptor : \A c \in votes[a] : c \in Vote
  /\ \A a \in Acceptor : \A c \in votes[a] : \A d \in votes[a] : c.b = d.b => c.v = d.v
  /\ \A b \in Ballot, v \in Value : CastFor(b, v) # {}
       => \A b2 \in Ballot, v2 \in Value : CastFor(b2, v2) # {}
              => b2 <= b /\ v2 = v

MCAcceptor == {x1, x2}
MCValue == {v1, v2}
MCQuorum == {{x1, x2}, {x1}}
MCBallot == 0..2

Symmetry ==
  {f \in [Acceptor -> Acceptor] : {f[x1], f[x2]} = {x1, x2}}

SpecTypeOK == [Acceptor |-> MCAcceptor, Value |-> MCValue, Quorum |-> MCQuorum, Ballot |-> MCBallot]
SpecTypeOK == Spec

Chosen == {v \in Value : \E Q \in Quorum : \A x \in Q : \E b \in Ballot : Vote(b, v) \in votes[x]}

MCSymmetry == Symmetry

ConsensusSpecBar == Spec /\ Inv /\ SpecTypeOK /\ MCSymmetry

====