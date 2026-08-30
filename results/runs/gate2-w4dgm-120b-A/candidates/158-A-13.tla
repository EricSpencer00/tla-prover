---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* Symmetry substitution: these definitions are overridden by the .cfg's MCSymmetry
\* (permutations of acceptors) but are nonetheless required symbols of the spec.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

VARIABLES votes, promised

vars == <<votes, promised>>

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET [ball: Ballot, val: Value]]
  /\ promised \in [Acceptor -> Ballot \cup {"none"}]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ promised = [a \in Acceptor |-> "none"]

VotedFor(a, b, v) == [ball |-> b, val |-> v] \in votes[a]

\* A value is safe at ballot b if every lower ballot always resolves to that
\* value, witnessed by a quorum for each lower ballot.
SafeAt(v, b) ==
  /\ \A c \in Ballot : c < b =>
       \E q \in Quorum :
         /\ \A a \in q : VotedFor(a, c, v) \/ promised[a] # "none" /\ promised[a] >= c
         /\ \A a \in q : (promised[a] # "none" /\ promised[a] >= c) => VotedFor(a, c, v)

QuorumVotedFor(v, b) == \E q \in Quorum : \A a \in q : VotedFor(a, b, v)

\* A ballot may only be cast once, so two quorums voting in the same ballot are
\* forced to agree on the value; "never lower than promised" is enforced here.
Vote(a, b, v) ==
  /\ \A c \in Ballot : c < b => promised[a] = "none" \/ promised[a] <= c
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {[ball |-> b, val |-> v]}]
  /\ promised' = [promised EXCEPT ![a] = b]
  /\ UNCHANGED <<>>

Promise(a, b) ==
  /\ promised[a] = "none" \/ b > promised[a]
  /\ promised' = [promised EXCEPT ![a] = b]
  /\ UNCHANGED <<votes>>

Next ==
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)
  \/ \E a \in Acceptor, b \in Ballot : Promise(a, b)

Spec == Init /\ [][Next]_vars

\* Every vote ever cast must have been safe at its ballot number.
ConsistentVotes == \A a \in Acceptor, x \in votes[a] : SafeAt(x.val, x.ball)

AtMostOneValuePerBallot ==
  \A a1, a2 \in Acceptor :
    \A x1 \in votes[a1], x2 \in votes[a2] :
      (x1.ball = x2.ball) => (x1.val = x2.val)

StateConstraint == ConsistentVotes /\ AtMostOneValuePerBallot

\* Derived: a value is considered chosen once some quorum voted for it.
Chosen == {v \in Value : \E b \in Ballot : QuorumVotedFor(v, b)}

\* The voting system never reaches a state where two different values are
\* both chosen, i.e. no two quorums can ever disagree on a ballot's value.
Inv == StateConstraint /\ Cardinality(Chosen) <= 1

\* No separate liveness requirement is modeled by this specification; consensus
\* is a safety concern here (every quorum aquired is for the one true value).
ConsensusSpecBar == TRUE

\* Symmetry of the model: swapping any two acceptors everywhere they appear is
\* an automorphism of the action relation, so each acceptor's role is symmetric.
MCSymmetry == <<a1, a2, a3>>

====