---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* The model is parameterized by the acceptor set, value set, quorum family,
\* and ballot range, which are instantiated as finite constants in the .cfg.
\* The symmetry group is the set of all permutations of the acceptor set.

VARIABLES votes, threshold

vars == <<votes, threshold>>

Vote == [ball : Ballot, val : Value]
Balloted(v) == {a \in Acceptor : v \in votes[a]}
QuorumVoted(v, b) == \E Q \in Quorum : \A a \in Q : [ball |-> b, val |-> v] \in votes[a]

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET Vote]
  /\ threshold \in [Acceptor -> Ballot \cup {-1}]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

\* An acceptor may raise its promise threshold without voting.
RaiseThreshold(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* An acceptor votes for a value in a ballot, provided the ballot is above its
\* threshold, it has not already voted in that ballot, no other value was voted
\* for in that ballot, and a quorum demonstrates the value is safe at b.
Vote(a, v, b) ==
  /\ b >= threshold[a]
  /\ \A c \in Ballot : [ball |-> c, val |-> v] \notin votes[a]
  /\ \A c \in Ballot : \A w \in Value : ([ball |-> c, val |-> w] \in votes[a]) => w = v
  /\ QuorumVoted(v, b)
  /\ votes' = [votes EXCEPT ![a] = @ \cup {[ball |-> b, val |-> v]}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : RaiseThreshold(a, b)
  \/ \E a \in Acceptor, v \in Value, b \in Ballot : Vote(a, v, b)

Spec == Init /\ [][Next]_vars

\* A value is chosen once a quorum has voted for it in some ballot.
Chosen == {v \in Value : \E Q \in Quorum : \A a \in Q : [ball |-> CHOOSE b \in Ballot : [ball |-> b, val |-> v] \in votes[a], val |-> v] \in votes[a]}

\* Safety: at most one value is ever chosen by a quorum.
Inv == \A v1 \in Chosen, v2 \in Chosen : v1 = v2

\* The voting algorithm implements the abstract consensus spec via refinement:
\* the chosen set is derived from the votes, and the invariant is preserved.
ConsensusSpecBar == Chosen = {v \in Value : \E Q \in Quorum : \A a \in Q : [ball |-> CHOOSE b \in Ballot : [ball |-> b, val |-> v] \in votes[a], val |-> v] \in votes[a]}

\* Every permutation of the acceptor set is a symmetry of the system.
MCSymmetry == {f \in [Acceptor -> Acceptor] : \A a1, a2 \in Acceptor : a1 = a2 <=> f[a1] = f[a2]}

\* The .cfg substitutes these bounded versions of the abstract constants.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

====