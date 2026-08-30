---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* A quorum is a nonempty set of acceptors; the overlap property (any two
\* quorums intersect) is assumed for the safety argument.
Quorums == { Q \in Quorum : Q # {} }

VARIABLES votes, threshold
vars == <<votes, threshold>>

HasVoted(a, b) == \E e \in votes[a] : e[1] = b

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ threshold \in [Acceptor -> Ballot]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

\* An acceptor may raise its promise threshold without voting, which blocks
\* it from participating in any earlier ballot thereafter.
RaiseThreshold(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* Ballot b is safe at value v if every lower ballot has a quorum that has
\* either already voted for v or can never vote in that lower ballot again.
BallotSafeAt(v, b) ==
  \A c \in 0 .. b - 1 : \E Q \in Quorums :
    \A a \in Q : \/ <<c, v>> \in votes[a] \/ threshold[a] >= c

\* Voting is constrained by the acceptor's current threshold and by the
\* unanimity requirement within a quorum for any given ballot.
CastVote(a, b, v) ==
  /\ b >= threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ ~HasVoted(a, b)
  /\ \A d \in Acceptor : d # a => ~HasVoted(d, b) \/ <<b, v>> \in votes[d]
  /\ BallotSafeAt(v, b)
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]

Next ==
  \/ \E a \in Acceptor : \E b \in Ballot : RaiseThreshold(a, b) \/ \E v \in Value : CastVote(a, b, v)
  \/ \E a \in Acceptor : \E b \in Ballot : \E v \in Value : CastVote(a, b, v)

Spec == Init /\ [][Next]_vars

\* No two different values are ever chosen by a quorum in any ballot.
QuorumConsistent ==
  \A a, d \in Acceptor : \A b \in Ballot : \A v, w \in Value :
    (<<b, v>> \in votes[a] /\ <<b, w>> \in votes[d]) => v = w

Inv == TypeOK /\ QuorumConsistent

\* The voting algorithm implements the abstract consensus spec: the chosen
\* set is derived from the votes and is always empty or a singleton.
ConsensusSpecBar == ConsensusSpec(MCAcceptor, MCValue, MCQuorum, MCBallot,
                                  CHOOSE v \in MCValue :
                                    \E Q \in MCQuorum : \A a \in Q : <<1, v>> \in votes[a])

\* Symmetry: any permutation of acceptor identities that leaves the quorum
\* family invariant is a symmetry of the system.
Permutations(S) == { f \in [S -> S] : \A x \in S : f[x] \in S }
MCSymmetry == { p \in Permutations(Acceptor) :
                  \A Q \in Quorum : { p[a] : a \in Q } \in Quorum }

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot
====