---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

(* The system has three types of participants: acceptors, values, quorums.     *)
(* Quorum-oversight is the only thing that stops two different values from    *)
(* ever both collecting a quorum of votes.                                    *)

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

Voters == {a1, a2, a3}
Values == {v1, v2}
AllQuorums == {q \in Quorum : TRUE}

\* A vote is a ballot number paired with the value it was cast for.
Vote == [ball : Ballot, val : Value]

VARIABLES votes, threshold

vars == <<votes, threshold>>

VoteSet == UNION {votes[a] : a \in Voters}
BallotOf(v) == v.ball
ChosenAt(b) == {v \in VoteSet : BallotOf(v) = b}

TypeOK ==
    /\ votes \in [Acceptor -> SUBSET Vote]
    /\ threshold \in [Acceptor -> Ballot \cup {-1}]

\* Both accepted: the balloting rule on its own, and the quorum-safety rule.
Accepted(v) ==
    /\ v \in VoteSet
    /\ Cardinality(ChosenAt(BallotOf(v))) >= 2

Init ==
    /\ votes = [a \in Voters |-> {}]
    /\ threshold = [a \in Voters |-> -1]

\* An acceptor never lowers its threshold, and never votes below it.
RaiseThreshold(a, b) ==
    /\ threshold[a] < b
    /\ threshold' = [threshold EXCEPT ![a] = b]
    /\ UNCHANGED votes

\* The ballot number may not be below the acceptor's threshold.
\* It also fails if some other vote for a different value already exists
\* in that ballot, or if no quorum demonstrates that this value is safe.
CastVote(a, v, b) ==
    /\ \A w \in votes[a] : w.ball < b
    /\ \A w \in VoteSet : (w.ball = b) => (w.val = v)
    /\ \E q \in AllQuorums :
         \A c \in Ballot : c < b => \E e \in q : [ball |-> c, val |-> v] \in votes[e]
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {[ball |-> b, val |-> v]}]
    /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
    \/ \E a \in Voters, b \in Ballot : RaiseThreshold(a, b)
    \/ \E a \in Voters, v \in Value, b \in Ballot : CastVote(a, v, b)

Spec == Init /\ [][Next]_vars

\* Chosen is derived from the votes, and the derived set is at most one.
Chosen = CHOOSE v \in VoteSet : \A w \in VoteSet : BallotOf(w) = BallotOf(v) => w.val = v

Inv ==
    /\ Accepted
    /\ \A w, z \in VoteSet : (w.ball = z.ball) => (w.val = z.val)
    /\ TypeOK

(* The voting algorithm refines an abstract consensus specification.  The    *)
(* derived "Chosen" must agree with the safe-value choice that the abstract  *)
(* spec defines for every ballot that has a quorum.                         *)
ConsensusSpecBar == Chosen = ConsensusSpecBar

MCAcceptor == {a1, a2, a3}
MCValue == {v1, v2}
MCQuorum == {q \in Quorum : TRUE}
MCBallot == Ballot

\* Symmetry-reducing permutations: every ballot can be renumbered down to 0.
MCSymmetry == {f \in [Acceptor -> Acceptor] : \A a \in Acceptor : f[a] \in Acceptor}
====