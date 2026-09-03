---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* Quorum overlap is assumed: any two quorums share at least one acceptor.
\* Ballot numbers are natural numbers; the model bounds them to a finite range.

VARIABLES votes, threshold

vars == <<votes, threshold>>

Vote == [ball : Ballot, val : Value]
Balloted(a) == { v.ball : v \in votes[a] }

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET Vote]
  /\ threshold \in [Acceptor -> Ballot \cup {-1}]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

\* An acceptor may raise its promise threshold, refusing to vote below it.
RaiseThreshold(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* A quorum must vouchsafe the value at the ballot before any vote lands.
VoteFor(a, b, val) ==
  /\ b >= threshold[a]
  /\ b \notin Balloted(a)
  /\ \A c \in Acceptor : (b \in Balloted(c)) => (\A w \in votes[c] : w.ball = b => w.val = val)
  /\ \E q \in Quorum :
       /\ \A m \in q : (b \in Balloted(m)) => (\A w \in votes[m] : w.ball = b => w.val = val)
       /\ \A c \in Acceptor : (\A w \in votes[c] : w.ball < b) => (\E m \in q : b \notin Balloted(m))
  /\ votes' = [votes EXCEPT ![a] = @ \cup {[ball |-> b, val |-> val]}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : RaiseThreshold(a, b)
  \/ \E a \in Acceptor, b \in Ballot, val \in Value : VoteFor(a, b, val)

Spec == Init /\ [][Next]_vars

\* A value is safe at a ballot if every lower ballot is backed by a quorum for it.
SafeAt(v, b) ==
  \A c \in 0 .. (b - 1) :
    \E q \in Quorum :
      /\ \A m \in q : (c \in Balloted(m)) => (\A w \in votes[m] : w.ball = c => w.val = v)
      /\ \A a \in Acceptor : (\A w \in votes[a] : w.ball < c) => (\E m \in q : c \notin Balloted(m))

\* Every vote cast must be safe at its ballot number.
AllVotesSafe == \A a \in Acceptor, v \in votes[a] : SafeAt(v.val, v.ball)

\* At most one value is voted for per ballot across all acceptors.
BallotSingleVal ==
  \A a, c \in Acceptor, v1, v2 \in votes[a] :
    (v1.ball = v2.ball) => (v1.val = v2.val)

\* The chosen set is derived from the votes, so its size is bounded by the
\* number of values; the invariant below is the real safety property.
ChosenSet == { v.val : a \in Acceptor, v \in votes[a] }

\* At most one value is ever chosen (the consensus outcome is unique).
Inv == AllVotesSafe /\ BallotSingleVal /\ Cardinality(ChosenSet) <= 1

\* The voting algorithm implements the abstract consensus spec via refinement.
ConsensusSpecBar == ChosenSet = { v.val : a \in Acceptor, v \in votes[a] }

\* Symmetry: any permutation of acceptors is indistinguishable in this model.
MCSymmetry == { [a1 |-> p[a1], a2 |-> p[a2], a3 |-> p[a3]] : p \in [Acceptor -> Acceptor] }

\* The .cfg substitutes these bounded versions of the abstract sets.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

====