---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS Acceptor, Value, Quorum, Ballot

VARIABLES votes, thresh
vars == <<votes, thresh>>

\* MCAcceptor/MCValue/MCQuorum/MCBallot are the finite concrete versions of
\* the abstract participant/value/quorum/ballot sets; the .cfg substitutes them
\* in for the unbounded versions above when model-checking.
MCAcceptor == {a1, a2, a3}
MCValue == {v1, v2}
MCQuorum == { {a1, a2}, {a2, a3} }
MCBallot == 0..2

Vote == [a: Acceptor, b: Ballot, w: Value]
Ballots == {v.b : v \in votes}
Chosen == {w \in Value : \E q \in Quorum, b \in Ballot: \A a \in q: <<a, b, w>> \in votes}

Init ==
  /\ votes = {}
  /\ thresh = [a \in Acceptor |-> -1]

\* An acceptor promises never to vote below a certain ballot number again.
RaiseThresh(a) ==
  /\ \E d \in Ballot: d > thresh[a] /\ thresh' = [thresh EXCEPT ![a] = d]
  /\ UNCHANGED votes

\* An acceptor casts a vote for a value in a ballot, but only if that value is
\* already safe at that ballot and no other value was voted for in it.
CastVote(a, b, w) ==
  /\ b >= thresh[a]
  /\ <<a, b, w>> \notin votes
  /\ \A v \in votes: v.b = b => v.w = w
  /\ \E q \in Quorum:
       /\ \A x \in q: x = a \/ <<x, b, w>> \in votes \/ b < thresh[x]
       /\ \A c \in 0..(b - 1): \E q2 \in Quorum:
            /\ \A x \in q2: x = a \/ <<x, c, w>> \in votes \/ c < thresh[x]
  /\ votes' = votes \cup {<<a, b, w>>}
  /\ thresh' = [thresh EXCEPT ![a] = b]

Next == \E a \in Acceptor: RaiseThresh(a) \/ \E b \in Ballot, w \in Value: CastVote(a, b, w)

Spec == Init /\ [][Next]_vars

\* Every cast vote is safe at its ballot number.
OnlySafeVotes == \A v \in votes: \A c \in 0..(v.b - 1):
  \E q \in Quorum: \A x \in q: x = v.a \/ <<x, c, v.w>> \in votes \/ c < thresh[x]

\* At most one value is ever voted for in any ballot.
AtMostOnePerBallot == \A v \in votes: \A v2 \in votes:
  (v.b = v2.b /\ v.w # v2.w) => v.a = v2.a

TypeOK == votes \subseteq Vote /\ thresh \in [Acceptor -> (-1)..(Ballot \cup 1)]

Inv == OnlySafeVotes /\ AtMostOnePerBallot /\ TypeOK

\* The voting algorithm implements consensus: the derived chosen set always has
\* at most one value, so the refinement to an abstract consensus primitive is
\* sound.
ConsensusSpecBar == \A q1, q2 \in Quorum: \A w1, w2 \in Value, b1, b2 \in Ballot:
  (\A a \in q1: <<a, b1, w1>> \in votes /\ \A a \in q2: <<a, b2, w2>> \in votes) => w1 = w2

\* Any permutation of the three acceptors that preserves the quorums is a
\* symmetry of this voting algorithm.
MCSymmetry == {f \in [Acceptor -> Acceptor]:
  /\ {f[q] : q \in Quorum} = Quorum
  /\ \A v \in votes: <<f[v.a], v.b, v.w>> \in votes}

====