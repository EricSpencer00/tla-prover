---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

ASSUME Acceptor = {a1, a2, a3}
ASSUME Value = {v1, v2}
ASSUME Ballot = Nat
ASSUME Quorum = {Q1, Q2}
ASSUME Q1 = {a1, a2}
ASSUME Q2 = {a2, a3}

VARIABLES vote, threshold

vars == << vote, threshold >>

TypeOK ==
  /\ vote \in [Acceptor -> SUBSET [ball : Ballot, val : Value]]
  /\ threshold \in [Acceptor -> Ballot]

Init ==
  /\ vote = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> 0]

Promising(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED vote

BallotMember(a, v, b) == [ball |-> b, val |-> v] \in vote[a]

QuorumVoted(v, b, Q) == \A a \in Q : BallotMember(a, v, b)

QuorumVotedSome(b) == \E v \in Value, Q \in Quorum : QuorumVoted(v, b, Q)

VoterSafe(a, v, b) ==
  /\ \A c \in Ballot : c < b => QuorumVotedSome(c)
  /\ \A a' \in Acceptor : BallotMember(a', v, b) => a' \in Quorum
  /\ QuorumVoted(v, b, Q1) \/ QuorumVoted(v, b, Q2)

Vote(a, v, b) ==
  /\ b >= threshold[a]
  /\ \A c \in Ballot : BallotMember(a, v, c) => c # b
  /\ \A a' \in Acceptor : BallotMember(a', v, b) => a' = a
  /\ \A a' \in Acceptor : BallotMember(a', v, b) => TRUE
  /\ \A a' \in Acceptor : BallotMember(a', v, b) => ~\E v' \in Value \ {v} : BallotMember(a', v', b)
  /\ \A a' \in Acceptor : \A v' \in Value : BallotMember(a', v', b) => v' = v
  /\ \A a' \in Acceptor : BallotMember(a', v, b) => TRUE
  /\ \A c \in Ballot : c < b => QuorumVotedSome(c)
  /\ VoterSafe(a, v, b)
  /\ vote' = [vote EXCEPT ![a] = vote[a] \cup {[ball |-> b, val |-> v]}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : Promising(a, b)
  \/ \E a \in Acceptor, v \in Value, b \in Ballot : Vote(a, v, b)

Spec == Init /\ [][Next]_vars

Chosen == {v \in Value : \E Q \in Quorum : QuorumVoted(v, 0, Q)}

AtMostOneChosen == \A v \in Chosen : \A Q \in Quorum : QuorumVoted(v, 0, Q)

VoteConsistent(a) ==
  /\ vote[a] \subseteq {x \in [ball : Ballot, val : Value] : VoterSafe(a, x.val, x.ball)}
  /\ \A m1 \in vote[a] : \A m2 \in vote[a] : m1.ball = m2.ball => m1.val = m2.val
  /\ \A m \in vote[a] : m.ball >= threshold[a]

Inv ==
  /\ AtMostOneChosen
  /\ \A a \in Acceptor : VoteConsistent(a)

ConsensusSpecBar == Spec => Inv

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

MCSymmetry == {f \in [Acceptor -> Acceptor] : \A a \in Acceptor : f[f[a]] = a}

====