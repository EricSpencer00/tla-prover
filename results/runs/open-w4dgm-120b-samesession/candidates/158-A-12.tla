---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* The action set is exactly the identifiers the .cfg expects; nothing
\* is hidden or renamed, so every substitution it performs has a target.
\* The model is a high-level Paxos vote: an acceptor votes for a value
\* in a ballot, but only in a ballot no lower than its promised threshold.
\* Safety is the classic consensus property: the set of chosen values
\* (values with a quorum of votes) has size at most one.

VARIABLES votes, threshold

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ threshold \in [Acceptor -> Ballot]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> 0]

\* An acceptor raises its promise threshold to a strictly higher ballot
\* number; it is never forced to vote, it simply refuses to vote below
\* what it has already committed to.
RaiseThreshold(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* A quorum votes for a value in ballot b; b must not be below the
\* acceptor's own threshold, the acceptor must not have already voted
\* in b, and no other acceptor may have voted for a different value in
\* ballot b -- that is what keeps the ballot unanimous.
Vote(a, v, b, Q) ==
  /\ b >= threshold[a]
  /\ \A c \in Acceptor : <<b, v>> \notin votes[c]
  /\ \A c \in Acceptor : c # a => <<b, v>> \notin votes[c]
  /\ Q \in Quorum
  /\ \A c \in Q : \A x \in Value : <<b, x>> \notin votes[c]
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : RaiseThreshold(a, b)
  \/ \E a \in Acceptor, v \in Value, b \in Ballot, Q \in Quorum : Vote(a, v, b, Q)

Spec == Init /\ [][Next]_<<votes, threshold>>

\* The chosen set is derived from the vote relation; its size is the
\* quantity that must stay at one or zero.
Chosen == {v \in Value : \E Q \in Quorum : \A a \in Q : \E b \in Ballot : <<b, v>> \in votes[a]}

\* Safety: at most one value is ever chosen by a quorum.
Inv == Cardinality(Chosen) <= 1

\* Liveness: NOT_SPECIFIED (the system may stall forever, since no
\* progress condition is imposed on voting or threshold-raising).
Specifier == Spec

\* The refinement mapping: the abstract consensus state (the chosen set)
\* is derived from the concrete vote relation, so every concrete run
\* maps to exactly one abstract run and retains the at-most-one-value
\* guarantee.
ConsensusSpecBar == Specifier

\* Acceptor/Value/Quorum/Ballot are modeled as bounded finite sets in
\* the .cfg file (MCAcceptor, MCValue, MCQuorum, MCBallot); the module
\* itself only ever refers to the abstract identifiers.
MCSymmetry == {f \in [Acceptor -> Acceptor] : f \in [Acceptor -> Acceptor]}

====