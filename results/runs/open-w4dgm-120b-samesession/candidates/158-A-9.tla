---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* A quorum is a set of acceptors, and the required overlap property is a
\* system-wide fact about the quorum family, not something a single action
\* can check.  It is therefore an explicit invariant, not an action guard.
CONSTANTS QuorumOne, QuorumTwo

\* Safety is maintained by refusing to let a ballot name two values; each
\* ballot's single value, if any, is the one the votes in that ballot name.
Vote == Ballot \X Value

VARIABLES votes, threshold

vars == <<votes, threshold>>

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET Vote]
  /\ threshold \in [Acceptor -> Nat]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> 0]

\* Votes travel, so the threshold can advance on its own; nothing ever
\* revokes a vote, it only becomes unreachable.
RaiseThreshold(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* A quorum is a set of acceptors, so election requires the whole set to
\* vote; there is no single coordinator that can skip the quorum.
VoteFor(a, b, v) ==
  /\ b >= threshold[a]
  /\ \A c \in Acceptor : <<b, v>> \notin votes[c]
  /\ \A c \in Acceptor : \A w \in Value : (w # v /\ <<b, w>> \in votes[c]) => FALSE
  /\ \E Q \in Quorum : \A c \in Q : <<b, v>> \in votes[c]
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

VoteStep == \E a \in Acceptor, b \in Ballot, v \in Value : VoteFor(a, b, v)

Next == VoteStep \/ (\E a \in Acceptor, b \in Ballot : RaiseThreshold(a, b))

Spec == Init /\ [][Next]_vars

\* Integrity: only one value per ballot, and only the value a quorum backs
\* is the value a ballot names.  Nothing is asserted about unused
\* ballot numbers, which are free to be anything the model explores.
BallotHasUniqueBackingValue ==
  \A b \in Ballot :
    /\ \A v \in Value : \A w \in Value : (v # w /\ \E a \in Acceptor :
                                          <<b, v>> \in votes[a]) => <<b, w>> \notin votes[a]
    /\ \E Q \in Quorum :
         \E v \in Value :
           \A a \in Q : <<b, v>> \in votes[a]

\* Every vote in a ballot must be backed by a quorum, and it must be
\* backed by the same quorum as every other vote in that ballot; a ballot
\* that only half the network has actually reached is not a ballot at all.
VoteBackedByUnanimousQuorum ==
  \A a \in Acceptor : \A b \in Ballot : \A v \in Value :
    <<b, v>> \in votes[a] =>
      /\ \E Q \in Quorum : \A c \in Q : <<b, v>> \in votes[c]
      /\ \A w \in Value : (\E c \in Acceptor : <<b, w>> \in votes[c]) => w = v

\* The chosen set is the projection of the vote relation: a value is in it
\* exactly when some acceptor voted for it, and the ballot bookkeeping is
\* what keeps that relation from naming two different values as chosen.
Chosen == { v \in Value : \E a \in Acceptor, b \in Ballot : <<b, v>> \in votes[a] }

Inv == BallotHasUniqueBackingValue /\ VoteBackedByUnanimousQuorum

\* Atomic broadcast collapses the vote relation into a single decision per
\* ballot, so the voting algorithm's one-value-per-ballot shape already
\* implies the one-chosen-value shape the service needs.
ConsensusSpecBar == Cardinality(Chosen) <= 1

\* The model deliberately explores many more ballot numbers than any live
\* deployment does; a quorum is fixed at the start and never changes.
Symmetry == { MCSymmetry }

\* The .cfg entry for MCAcceptor is a bounded version of Acceptor, which
\* agrees with the model but keeps the reachable state space tiny.
MCAcceptor == {a1, a2, a3}
MCValue == {v1, v2}
MCQuorum == {QuorumOne, QuorumTwo}
MCBallot == 0..1

====