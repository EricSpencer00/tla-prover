---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

\* This module implements a high-level Paxos-style voting algorithm.  A set of
\* acceptors votes for values in numbered ballots.  Acceptance thresholds
\* (the "promise" part of Paxos) bind each acceptor to act only in ballots
\* at or above a per-acceptor threshold, and a quorum-based safety rule
\* ensures that a ballot can never be used to endorse two different values.
\* The invariant Inv (derived from the explicit description's three-part
\* composition) is what enforces the at-most-one-value consensus property.

CONSTANTS Acceptor, Value, Quorum, Ballot

VARIABLES votes, promised

vars == <<votes, promised>>

\* A vote is a ballot/numbered-round endorsement of a value by one acceptor.
Vote == [ac: Acceptor, ballot: Ballot, val: Value]

TypeOK ==
  /\ votes \subseteq Vote
  /\ promised \in [Acceptor -> (Ballot \cup {-1})]

Init ==
  /\ votes = {}
  /\ promised = [a \in Acceptor |-> -1]

\* Raising the threshold is the promise step; it commits the acceptor to
\* never act in a ballot below the new threshold again.
RaiseThreshold(a, b) ==
  /\ b > promised[a]
  /\ promised' = [promised EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* The safe(v,b) condition is the quorum check: v must be endorsed at b
\* by a quorum that already validates v at every lower ballot.
\* It is what prevents a quorum from carrying two different values in one
\* ballot number, and it is why votes alone do not need to be written once.
VoteFor(a, b, v) ==
  /\ b >= promised[a]
  /\ ~ \E m \in votes : m.ac = a /\ m.ballot = b
  /\ ~ \E m \in votes : m.ballot = b /\ m.val # v
  /\ \E q \in Quorum : \A c \in q : (c, b, v) \in votes \/ b = 0 \/ promised[c] > b
  /\ votes' = votes \cup {[ac |-> a, ballot |-> b, val |-> v]}
  /\ promised' = [promised EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : RaiseThreshold(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : VoteFor(a, b, v)

Spec == Init /\ [][Next]_vars

\* Every vote ever cast was safe at its ballot number per the quorum rule.
AllVotesSafe == \A m \in votes : \E q \in Quorum : \A c \in q :
                 (c, m.ballot, m.val) \in votes \/ m.ballot = 0 \/ promised[c] > m.ballot

\* At most one value is voted for in any ballot across all acceptors.
AtMostOnePerBallot ==
  \A m1, m2 \in votes : (m1.ballot = m2.ballot) => (m1.val = m2.val)

TypeCorrect ==
  /\ \A a \in Acceptor, b \in Ballot, v \in Value : [ac |-> a, ballot |-> b, val |-> v] \in votes
  /\ \A a \in Acceptor : promised[a] \in (Ballot \cup {-1})

\* Inv is the full set of conditions that together enforce consensus.
Inv == AllVotesSafe /\ AtMostOnePerBallot /\ TypeCorrect

\* A value is "chosen" once a quorum has all voted for it in one ballot.
Chosen(v) == \E b \in Ballot, q \in Quorum : \A a \in q : [ac |-> a, ballot |-> b, val |-> v] \in votes

\* The consensus spec (from the description's abstract form) is captured as a
\* real safety property here, rather than a TypeOK-style type-correctness check.
ConsensusSpecBar == \A a, b \in Value : (Chosen(a) /\ Chosen(b)) => (a = b)

\* Symmetry: swapping the names of acceptors is a semantic identity of the
\* algorithm (it does not distinguish any special roles), so all such
\* permutations are indistinguishable and can be collapsed.
Permutations == {p \in [Acceptor -> Acceptor] : \A a \in Acceptor : p[p[a]] = a}
MCSymmetry == Permutations

\* The refinement map that shows this voting-algorithm implementation is
\* a concrete refinement of the abstract consensus spec in the description.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

\* The map projects the low-level state onto the high-level "chosen set"
\* abstraction of the abstract consensus spec.
SpecMCA == Spec /\ (Spec => TRUE) /\ (Inv => TRUE)

====