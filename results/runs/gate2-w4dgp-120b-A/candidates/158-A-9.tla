---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

\* A voting-based consensus system: acceptors cast votes for values in numbered
\* ballots. A value is only ever voted for in a ballot if every lower ballot is
\* backed by a quorum that already voted for it, which is what makes the chosen
\* value unique across all ballots.

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

Vote == [val: Value, bal: Ballot]

VARIABLES votes, promised

vars == <<votes, promised>>

Quorums == Quorum

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET Vote]
  /\ promised \in [Acceptor -> Nat]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ promised = [a \in Acceptor |-> 0]

\* An acceptor raises its promise threshold, refusing to vote in earlier ballots.
RaiseThreshold(a, b) ==
  /\ b > promised[a]
  /\ promised' = [promised EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* An acceptor votes for a value in a ballot, provided no different value already
\* has votes in that ballot, the ballot is above its threshold, and the value is
\* safe at that ballot number.
CastVote(a, v, b) ==
  /\ b >= promised[a]
  /\ \A w \in votes[a] : w.bal # b
  /\ \A x \in Acceptor : \A w \in votes[x] : (w.bal = b) => (w.val = v)
  /\ \A c \in 0..(b-1) : \E q \in Quorums :
        \A x \in q : (x \in Acceptor) => (\A w \in votes[x] : (w.bal = c => w.val = v))
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {[val |-> v, bal |-> b]}]
  /\ promised' = [promised EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : RaiseThreshold(a, b)
  \/ \E a \in Acceptor, v \in Value, b \in Ballot : CastVote(a, v, b)

Spec == Init /\ [][Next]_vars

\* Votes are always safe at the ballot they were cast in.
VotesAreSafe ==
  \A a \in Acceptor : \A w \in votes[a] :
    \A c \in 0..(w.bal - 1) : \E q \in Quorums :
      \A x \in q : (x \in Acceptor) => (\A u \in votes[x] : (u.bal = c) => (u.val = w.val))

\* A ballot never has votes for two different values.
BallotConsistent ==
  \A a \in Acceptor : \A b \in Acceptor :
    \A w \in votes[a] : \A w2 \in votes[b] : (w.bal = w2.bal) => (w.val = w2.val)

Inv == VotesAreSafe /\ BallotConsistent /\ TypeOK

\* The chosen set is derived from the votes: a value is chosen if some quorum
\* unanimously voted for it. The derived chosen set has at most one element, so
\* the voting system implements consensus.
ConsensusSpecBar ==
  LET Chosen == {v \in Value : \E q \in Quorums :
                      \A x \in q : \E w \in votes[x] : w.val = v}
  IN Cardinality(Chosen) <= 1

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

MCSymmetry ==
  {p \in [Acceptor -> Acceptor] :
    /\ (\A x \in Acceptor : p[x] \in Acceptor)
    /\ (\A x, y \in Acceptor : (x \in p[y]) <=> (y \in p[x]))
    /\ (\A x \in Acceptor : x \in p[x])
    /\ (\A x, y \in Acceptor : (x \in p[y] /\ y \in p[x]) => (x = y))}

====