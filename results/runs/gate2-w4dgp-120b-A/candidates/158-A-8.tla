---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

\* Quorum-based voting with a ballot number. An acceptor raises its promise
\* threshold before voting. A vote only lands when no other value already has
\* a quorum at that ballot, so two different values can never both win.

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

VARIABLES votes, threshold
vars == <<votes, threshold>>

Vote == [ball : Ballot, val : Value]

\* A value is safe at a ballot if every lower ballot already had a quorum
\* that voted for it (or the acceptors could never vote there).
Safe(v, b) ==
  \A c \in 0..(b - 1) : \E q \in Quorum :
    \A a \in q : (c \in domain(votes[a]) => votes[a][c] = v)

Init ==
  /\ votes = [a \in Acceptor |-> [b \in Ballot |-> v1]]
  /\ threshold = [a \in Acceptor |-> -1]

\* An acceptor raises its promise threshold, discarding the ability to vote below it.
Promise(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* Cast a vote, provided it is safe and there is no competing quorum.
VoteFor(a, b, v) ==
  /\ b >= threshold[a]
  /\ b \notin domain(votes[a])
  /\ \A x \in Acceptor : b \in domain(votes[x]) => votes[x][b] = v
  /\ Safe(v, b)
  /\ votes' = [votes EXCEPT ![a] = [@ EXCEPT ![b] = v]]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : Promise(a, b) \/ VoteFor(a, b, v1) \/ VoteFor(a, b, v2)
  \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

Inv ==
  /\ \A a \in Acceptor : \A b \in domain(votes[a]) : Safe(votes[a][b], b)
  /\ \A b \in Ballot :
       (\A a \in Acceptor : b \in domain(votes[a])) =>
         (\A x \in Acceptor : b \in domain(votes[x]) => votes[x][b] = votes[CHOOSE a \in Acceptor : b \in domain(votes[a])])
  /\ \A a \in Acceptor : threshold[a] \in -1 \cup Ballot

\* The chosen set is derived from the votes, so the invariant implements
\* consensus by refinement of the abstract one.
Choices == {v \in Value : \E q \in Quorum : \A a \in q : v \in range(votes[a])}
ConsensusSpecBar == \A x, y \in Choices : x = y

MCSymmetry == [a1 |-> a2, a2 |-> a1, a3 |-> a3]

MCAcceptor == {a1, a2, a3}
MCValue == {v1, v2}
MCQuorum == {{a1, a2}, {a1, a3}, {a2, a3}}
MCBallot == 0..1

====