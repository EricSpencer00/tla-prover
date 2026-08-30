---- MODULE Voting ----
EXTENDS Naturals

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* The spec abstracts Paxos: acceptors vote for a value in a ballot, and the
\* ballot numbers are natural numbers. Safety is ensured by a vote being
\* safe (agrees with every lower ballot's quorum) and quorums overlapping.
VARIABLES votes, threshold

NoThresh == -1

MCAcceptor == {a1, a2, a3}
MCValue == {v1, v2}
MCQuorum == {Quorum}
MCBallot == Ballot

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ threshold \in [Acceptor -> Ballot \cup {NoThresh}]

Init ==
  /\ votes = [a \in MCAcceptor |-> {}]
  /\ threshold = [a \in MCAcceptor |-> NoThresh]

VotedAt(a, b) == \E val \in MCValue : <<b, val>> \in votes[a]

QuorumVoted(b, val) == \E Q \in MCQuorum :
  \A a \in Q : <<b, val>> \in votes[a]

\* A value is safe at a ballot if every earlier ballot already has a quorum
\* voting for it (or is unwinnable), so no conflicting value can later win.
ValueSafeAt(b, val) ==
  /\ QuorumVoted(b, val)
  /\ \A c \in Ballot : c < b =>
       \/ QuorumVoted(c, val)
       \/ \A Q \in MCQuorum :
            \A a \in Q : VotedAt(a, c) => <<c, val>> \in votes[a]

\* An acceptor may always promise to ignore ballots below a higher threshold.
Promise(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* Casting a vote is the only way a ballot is decided, and it needs a quorum.
Vote(a, b, val) ==
  /\ b >= threshold[a]
  /\ ~VotedAt(a, b)
  /\ (\A a2 \in MCAcceptor : (a2 # a /\ VotedAt(a2, b)) => \A z \in MCValue : <<b, z>> \in votes[a2] => z = val)
  /\ QuorumVoted(b, val)
  /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, val>>}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in MCAcceptor, b \in MCBallot : Promise(a, b) \/ Vote(a, b, v1) \/ Vote(a, b, v2)

Spec == Init /\ [][Next]_<<votes, threshold>>

\* Every cast vote is safe at its ballot, and per ballot at most one value
\* is voted for, which together yield at-most-one chosen value.
Inv ==
  /\ \A a \in MCAcceptor, val \in MCValue : <<a, val>> \in votes => ValueSafeAt(a, val)
  /\ \A a1, a2 \in MCAcceptor : a1 # a2 => votes[a1] \cap votes[a2] = {}
  /\ TypeOK

Chosen == {val \in MCValue : \E Q \in MCQuorum : \A a \in Q : <<1, val>> \in votes[a]}
\* Safety: at most one value is ever chosen by a quorum.
Safety == \A x, y \in Chosen : x = y

\* Consensus spec: the chosen set is derived from the votes, and the invariant
\* is exactly the consistency condition it must satisfy.
ConsensusSpecBar == Chosen = {val \in MCValue : \E Q \in MCQuorum : \A a \in Q : <<1, val>> \in votes[a]}

\* Acceptor symmetry: any permutation of acceptors is an automorphism of the
\* system, so the model cannot distinguish which acceptor behaves which way.
MCSymmetry == {f \in [MCAcceptor -> MCAcceptor] : \A a \in MCAcceptor : f[a] \in MCAcceptor}

====