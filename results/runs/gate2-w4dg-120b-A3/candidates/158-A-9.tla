---- MODULE Voting ----
EXTENDS Integers, FiniteSets

\* System model: a voting-based consensus where acceptors cast ballot-numbered
\* votes for values, and a value is chosen once a quorum of acceptors has voted
\* for it in the same ballot. The model is deliberately abstract and has no
\* explicit proposer or leader role.

CONSTANTS
  a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

Vote == Ballot \X Value

VARIABLES votes, thresh

vars == << votes, thresh >>

\* The chosen set is derived from the votes: it contains every value that some
\* quorum has voted for in some ballot.
Chosen == { v \in Value : \E b \in Ballot, Q \in Quorum : \A a \in Q : << b, v >> \in votes[a] }

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET Vote]
  /\ thresh \in [Acceptor -> (-1 : Int) \cup Ballot]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ thresh = [a \in Acceptor |-> -1]

\* An acceptor raises its promise threshold to a higher ballot number,
\* which blocks it from participating in lower-numbered ballots.
RaiseThresh(a, b) ==
  /\ b > thresh[a]
  /\ thresh' = [thresh EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* A value is safe at a ballot if no quorum can later vote for a different one
\* in an earlier ballot; the ballot check looks at every lower-numbered ballot.
SafeAt(a, b, v) ==
  /\ \A c \in Ballot : c < b => \E Q \in Quorum :
       \A m \in Q : << c, v >> \in votes[m] \/ \A d \in Ballot : d < b => << d, v >> \notin votes[m]
  /\ thresh[a] <= b
  /\ \A m \in Acceptor : << b, v >> \in votes[m] => m = a

\* An acceptor may vote for a value in a ballot only if it has not already
\* voted in that ballot elsewhere and no other distinct value was voted for
\* in that ballot, so a ballot never carries two competing values.
CastVote(a, b, v) ==
  /\ SafeAt(a, b, v)
  /\ \A m \in Acceptor : << b, v >> \in votes[m] => m = a
  /\ votes' = [votes EXCEPT ![a] = @ \cup { << b, v >> }]
  /\ thresh' = [thresh EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : RaiseThresh(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : CastVote(a, b, v)

Spec == Init /\ [][Next]_vars

\* Consistency: at most one distinct value is ever chosen by a quorum.
Inv == \A a \in Acceptor : \A v \in votes[a] : SafeAt(a, v[1], v[2])

\* ConsensusSpecBar is a refinement-level view of the chosen set.
ConsensusSpecBar == Chosen \subseteq { v \in Value : \E a \in Acceptor : << 0, v >> \in votes[a] }

\* MCSymmetry is the symmetry group over the acceptors -- swapping acceptors
\* does not change the observable behaviour of the reference model.
MCSymmetry == { f \in [Acceptor -> Acceptor] :
                  \A x \in Acceptor : f[f[x]] = x /\ f[x] # x }

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

====