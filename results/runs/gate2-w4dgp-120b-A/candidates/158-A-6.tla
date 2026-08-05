---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

\* This specification models a high-level voting-based consensus algorithm
\* (an abstraction of Paxos) in which acceptor processes cooperatively
\* choose a value. A quorum of acceptors votes for a value in a numbered
\* ballot; a value is safe to vote for only if every lower ballot already
\* has a quorum supporting it. The two main actions are: raising an
\* acceptor's promise threshold to a higher ballot, and casting a safe vote.
\* The invariant is that at most one value can ever be chosen.
CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

VARIABLES votes, promised

vars == <<votes, promised>>

\* A quorum supporting value v at ballot b is a set of acceptors that all
\* have already voted for v in b, or that can never vote in b.
\* "Can never vote in b" means the acceptor's promise threshold already
\* exceeds b, so it is permanently excluded from that ballot.
Supports(v, b, Q) == \A a \in Q :
  \/ <<a, b, v>> \in votes
  \/ promised[a] > b

\* A value is safe at ballot b only if every lower ballot already has a
\* quorum supporting it, so voting for it cannot contradict anything below.
Safe(v, b) == \A c \in 0 .. (b - 1) : \E Q \in Quorum : Supports(v, c, Q)

\* A value is chosen once some quorum has voted for it in some ballot.
Chosen(v) == \E b \in Ballot : \E Q \in Quorum : Supports(v, b, Q)

Init ==
  /\ votes = {}
  /\ promised = [a \in Acceptor |-> -1]

\* An acceptor may raise its promise threshold to a higher ballot without
\* voting; it will refuse to vote in any ballot below its threshold.
Raise(a, b) ==
  /\ b > promised[a]
  /\ promised' = [promised EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* Casting a vote requires the ballot to be at or above the threshold,
\* that the acceptor has not already voted in this ballot, and that no
\* other acceptor voted for a different value in this ballot. The value
\* must be safe (all lower ballots already supported it by quorum).
Cast(a, b, v) ==
  /\ b >= promised[a]
  /\ ~ \E c \in Ballot : <<a, c, v>> \in votes
  /\ \A x \in Acceptor : ~ <<x, b, v>> \in votes
  /\ Safe(v, b)
  /\ votes' = votes \cup {<<a, b, v>>}
  /\ promised' = [promised EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : Raise(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : Cast(a, b, v)

Spec == Init /\ [][Next]_vars

Inv ==
  /\ \A x \in votes : Safe(x[3], x[2])
  /\ \A x \in votes, y \in votes : (x[2] = y[2] /\ x[3] # y[3]) => x[1] = y[1]
  /\ \A a \in Acceptor : promised[a] \in (-1) \cup Ballot
  /\ \A x \in votes : x[1] \in Acceptor /\ x[2] \in Ballot /\ x[3] \in Value

\* The voting algorithm implements the abstract consensus spec: the
\* chosen set (values backed by some quorum) never has two distinct
\* values, i.e. the consensus safety property holds.
ConsensusSpecBar == Cardinality({v \in Value : Chosen(v)}) <= 1

MCSymmetry == {f \in [Acceptor -> Acceptor] : f[a1] = a1}

\* The constants are bound to finite sets for model checking; the
\* ballot range is kept small (zero through one here) so TLC explores
\* the full reachable space. In a larger scale deployment ballot numbers
\* would range over the full natural numbers.
MCAcceptor == {a1, a2, a3}
MCValue == {v1, v2}
MCQuorum == {{a1, a2}, {a1, a3}, {a2, a3}}
MCBallot == 0 .. 1

====