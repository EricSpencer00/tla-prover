---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* MCAcceptor, MCValue, MCQuorum, MCBallot are substitution operators: they
\* are defined as operators whose right-hand side is the constant set, so the
\* .cfg can replace them with a bounded version for model checking.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

VARIABLES votes, th

vars == << votes, th >>

VotePairs == [ball : Ballot, val : Value]
Quorums == Quorum
Acceptors == Acceptor
Ballots == Ballot

TypeOK ==
  /\ votes \in [Acceptors -> SUBSET VotePairs]
  /\ th \in [Acceptors -> Ballots \cup {-1}]

Init ==
  /\ votes = [a \in Acceptors |-> {}]
  /\ th = [a \in Acceptors |-> -1]

\* An acceptor may raise its promise threshold, opting out of lower ballots.
RaiseThreshold(a, b) ==
  /\ b > th[a]
  /\ th' = [th EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* A vote is safe at a ballot if every lower ballot already had a safe
\* supporting quorum for the same value.
SafeAt(a, b, v) ==
  /\ \A c \in Ballots : c < b => \E Q \in Quorums :
        /\ SetOfVoters(c, v) \subseteq Q
        /\ Q \subseteq {x \in Acceptors : th[x] <= c}
  /\ Cardinality({x \in Acceptors : \E p \in votes[x] : p.ball = b}) < 3

\* A quorum of acceptors votes for a value in ballot b, under the safety
\* and promise constraints, and the voting acceptor's threshold is raised.
CastVote(a, b, v) ==
  /\ b >= th[a]
  /\ \A p \in votes[a] : p.ball # b
  /\ ~ \E q \in Acceptors : \E p \in votes[q] : p.ball = b /\ p.val # v
  /\ SafeAt(a, b, v)
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {[ball |-> b, val |-> v]}]
  /\ th' = [th EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptors : \E b \in Ballots : RaiseThreshold(a, b)
  \/ \E a \in Acceptors : \E b \in Ballots : \E v \in Values : CastVote(a, b, v)

Spec == Init /\ [][Next]_vars

\* An acceptor has voted for at most one value per ballot.
PerBallotVoteUniqueness ==
  \A a \in Acceptors : \A p1, p2 \in votes[a] :
    (p1.ball = p2.ball) => (p1.val = p2.val)

\* Every vote in the system is safe at its ballot number.
AllVotesSafe ==
  \A a \in Acceptors : \A p \in votes[a] : SafeAt(a, p.ball, p.val)

\* At most one value wins a quorum across all ballots.
AtMostOneChosen ==
  \A Q1, Q2 \in Quorums, v1, v2 \in Values :
    (SetOfVoters(\A v \in Values : v, v1) \subseteq Q1 /\ SetOfVoters(\A v \in Values : v, v2) \subseteq Q2) =>
      v1 = v2

SetOfVoters(b, v) == {x \in Acceptors : [ball |-> b, val |-> v] \in votes[x]}

ChosenValues == {v \in Values : \E Q \in Quorums : SetOfVoters(\A b \in Ballots : b, v) \subseteq Q}

Inv == PerBallotVoteUniqueness /\ AllVotesSafe /\ AtMostOneChosen

\* The voting algorithm implements the abstract consensus spec via a
\* refinement that extracts ChosenValues from the votes.
QuorumConsensus ==
  \A b \in Ballots : \E v \in ChosenValues : SetOfVoters(b, v) # {}

\* The .cfg's symmetry set: permutations of acceptors that leave the
\* configuration unchanged (renaming of participants).
MCSymmetry == {f \in [Acceptors -> Acceptors] : \A a \in Acceptors : f[a] = a}

====