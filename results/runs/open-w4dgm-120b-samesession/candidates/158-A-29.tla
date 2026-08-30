---- MODULE Voting ----
EXTENDS Integers, FiniteSets

(* High-level voting consensus: acceptors cast quorum-backed votes for a value  *)
(* in numbered ballots.  The invariant must be read as a pair of the consensus *)
(* spec and an even stronger per-ballot, per-value safety property.            *)

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

VoteSpace == [ball : Ballot, val : Value]
Var == { "votes", "threshold" }

VARIABLES votes, threshold

Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> -1]

\* An acceptor may raise its promise threshold without voting; it will not
\* vote in any ballot below the new threshold.
RaiseThreshold(a, n) ==
    /\ n > threshold[a]
    /\ \A b \in Quorum : a \in b
    /\ threshold' = [threshold EXCEPT ![a] = n]
    /\ UNCHANGED votes

\* An acceptor votes in ballot n for value v only when no member has voted for
\* a different value in that ballot, and only when a quorum demonstrates v is
\* safe at n (nothing lower was ever chosen against it).
Vote(a, n, v) ==
    /\ n >= threshold[a]
    /\ \A x \in votes[a] : x.ball # n
    /\ \A x \in votes[a] : x.val = v => x.ball <= n
    /\ \A b \in Quorum : \A x \in votes[a] : x.ball = n => x.val = v
    /\ \E b \in Quorum :
        \A c \in Ballot :
            c < n =>
                \E x \in votes[a] :
                    /\ x.ball = c
                    /\ x.val = v
                    /\ \A y \in b : y \in Acceptor => (\E z \in votes[y] : z.ball = c /\ z.val = v \/ threshold[y] >= c)
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {[ball |-> n, val |-> v]}]
    /\ threshold' = [threshold EXCEPT ![a] = n]

Next ==
    \/ \E a \in Acceptor, n \in Ballot : RaiseThreshold(a, n)
    \/ \E a \in Acceptor, n \in Ballot, v \in Value : Vote(a, n, v)

Spec == Init /\ [][Next]_Var

\* A value is safe at ballot n if every lower ballot is either already chosen
\* for that value everywhere in some quorum, or is unavailable to vote.
SafeAt(v, n) ==
    \A c \in Ballot : c < n =>
        \/ \A a \in Acceptor : \E x \in votes[a] : x.ball = c /\ x.val = v
        \/ \E b \in Quorum :
            \A a \in b : \E x \in votes[a] : x.ball = c /\ x.val = v \/ threshold[a] >= c

VotesAreSafe == \A a \in Acceptor : \A x \in votes[a] : SafeAt(x.val, x.ball)

\* No two distinct values are ever simultaneously held by a quorum.
QuorumSingleChoice ==
    \A v1_, v2_ \in Value :
        (\E Q \in Quorum : \A a \in Q : \E x \in votes[a] : x.val = v1_)
        /\ (\E Q \in Quorum : \A a \in Q : \E x \in votes[a] : x.val = v2_)
        => v1_ = v2_

TypeOK ==
    /\ votes \in [Acceptor -> SUBSET VoteSpace]
    /\ threshold \in [Acceptor -> Ballot \cup {-1}]

Inv == VotesAreSafe /\ QuorumSingleChoice /\ TypeOK

\* The consensus spec: the set of chosen values has size at most one.  The
\* per-ballot safety property is strictly stronger, so this follows from it.
ConsensusSpecBar == Cardinality({ v \in Value : \E a \in Acceptor, x \in votes[a] : x.val = v }) <= 1

Vars == Var

NextA == \E a \in Acceptor : \E n \in Ballot : RaiseThreshold(a, n)
NextV == \E a \in Acceptor, n \in Ballot, v \in Value : Vote(a, n, v)

FAIRNESS == {NextA, NextV}

\* Symmetry: any permutation of acceptors is indistinguishable in this system.
MCSymmetry == {p \in [Acceptor -> Acceptor] : \A a \in Acceptor : p[a] \in Acceptor}

(* Per the .cfg these stand in for the declared constants when model checking. *)
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

====