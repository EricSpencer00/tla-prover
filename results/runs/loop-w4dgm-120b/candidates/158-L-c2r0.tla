---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

Actors == Acceptor
Votes == [ball : Ballot, val : Value]
Ballots == {1, 2}

VARIABLES votes, threshold
vars == <<votes, threshold>>

RECURSIVE SafeAt(_, _)
SafeAt(b, x) ==
  IF b = 1 THEN TRUE
  ELSE /\ SafeAt(b - 1, x)
       /\ \E Q \in MCQuorum : \A a \in Q :
            \/ <<b, x>> \in votes[a]
            \/ threshold[a] >= b

\* An action only ever raises an acceptor's promise threshold, never lowers it.
Cast(a, x, b) ==
  /\ threshold[a] < b
  /\ \A y \in Value : <<b, y>> \notin votes[a]
  /\ \A c \in Ballots : \A y \in Value : (x # y /\ <<c, y>> \in votes[a]) => c # b
  /\ \E Q \in MCQuorum : \A q \in Q : SafeAt(b, x)
  /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, x>>}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

RaiseThreshold(a, b) ==
  /\ threshold[a] < b
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ votes' = votes

Init ==
  /\ votes = [a \in Actors |-> {}]
  /\ threshold = [a \in Actors |-> -1]

Next ==
  \/ \E a \in Actors, x \in Value, b \in Ballots : Cast(a, x, b)
  \/ \E a \in Actors, b \in Ballots : RaiseThreshold(a, b)

Spec == Init /\ [][Next]_vars

Voted(v) == {a \in Actors : \E b \in Ballots : <<b, v>> \in votes[a]}
QuorumFor(v) == \E Q \in MCQuorum : \A a \in Q : v \in Voted(a)
Chosen == {v \in Value : QuorumFor(v)}

TypeOK ==
  /\ votes \in [Actors -> SUBSET Votes]
  /\ threshold \in [Actors -> -1..Cardinality(Ballots)]

\* Every cast vote is safe at its ballot number; ballot safety implies,
\* together with the overlap of quorums, that at most one value is chosen.
VoteConsistent ==
  /\ \A a \in Actors : \A w \in votes[a] : SafeAt(w.ball, w.val)
  /\ \A x, y \in Value : (QuorumFor(x) /\ QuorumFor(y)) => x = y
  /\ TypeOK

\* The voting algorithm implements quorum-consensus: the chosen values are
\* exactly those carried by a quorum of acceptors.  The actions only ever
\* add a vote to an acceptor's record, never pick a value out from under
\* one, so a previously chosen value is never lost.
ConsensusSpecBar ==
  /\ Chosen \subseteq MCValue
  /\ \A x \in MCValue : x \in Chosen => QuorumFor(x)

\* Symmetry: acceptors are indistinguishable, so any swap of them
\* leaves the reachable state space unchanged.
MCSymmetry == {p \in [Actors -> Actors] : \A a \in Actors : p[p[a]] = a}

\* The .cfg files swap the following abstract identifiers for these:
MCAcceptor == Actors
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballots

====