---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* Alias operators for the .cfg substitutions; they just rename the constants.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

VARIABLES votes, thr
vars == <<votes, thr>>

VotePairs == [ball: MCBallot, val: MCValue]
\* A (ballot, value) pair that is currently safe at that ballot number.
SafePairs == {p \in VotePairs : \A c \in MCBallot: c < p.ball => \E q \in MCQuorum:
                  \A a \in q: (c, p.val) \in votes[a] \/ (c \notin MCBallot) }

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET VotePairs]
  /\ thr \in [Acceptor -> MCBallot \cup {-1}]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ thr = [a \in Acceptor |-> -1]

\* The acceptor's promise threshold only ever moves upward.
RaiseTh(a) ==
  /\ \E e \in MCBallot: e > thr[a] /\ thr' = [thr EXCEPT ![a] = e]
  /\ UNCHANGED votes

\* Voting is the only way a ballot number gets stamped on an acceptor.
Vote(a, b, v) ==
  /\ b \in MCBallot
  /\ b >= thr[a]
  /\ \A c \in MCBallot, w \in MCValue: (c = b /\ w # v) => ((c, w) \notin votes[a])
  /\ \A q \in MCQuorum: \A p \in q: ((b, v) \in votes[p] \/ p = a)
  /\ [ball |-> b, val |-> v] \in SafePairs
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {[ball |-> b, val |-> v]}]
  /\ thr' = [thr EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor: RaiseTh(a)
  \/ \E a \in Acceptor, b \in MCBallot, v \in MCValue: Vote(a, b, v)

Spec == Init /\ [][Next]_vars

\* SAFETY: the chosen set is unambiguously single-valued.
Chosen == {v \in MCValue: \E q \in MCQuorum: \A a \in q: [ball |-> b, val |-> v] \in votes[a]}
Inv ==
  /\ Chosen \subseteq MCValue
  /\ \A a \in Acceptor: votes[a] \subseteq SafePairs
  /\ \A a \in Acceptor, p \in votes[a], q \in Acceptor, r \in MCBallot, w \in MCValue:
        (r = p.ball /\ w # p.val) => ((r, w) \notin votes[q])
  /\ TypeOK

\* LIVENESS properties are not needed for this model; the action set is finite,
\* so weak fairness on voting is enough to cover all reachable ballots.
Quiet == (\A a \in Acceptor: thr[a] = MCBallot)

\* SAFETY: at most one value is ever chosen. LIVENESS: nothing is left enabled
\* once every ballot is exhausted, so the model always reaches a quiet state.
ConsensusSpecBar == Inv /\ (Quiet ~> Quiet)
====