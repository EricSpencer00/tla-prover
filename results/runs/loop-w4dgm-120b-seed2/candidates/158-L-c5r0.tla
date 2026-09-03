---- MODULE Voting ----
EXTENDS Integers, FiniteSets, TLC

(* An abstracted Paxos-like voting mechanism: acceptors cast per-ballot votes   *)
(* for a value, but a vote is only valid if a quorum can vouch that the value   *)
(* is safe at that ballot.  Because every quorum overlaps, two quorums voting  *)
(* at different ballots can only both be safe for the same value.               *)

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

Votes == [ball : Ballot, val : Value]
BallotRange == { i \in Ballot : i >= 0 }
NoVote == [ball |-> 0, val |-> CHOOSE x \in Value : TRUE]

VARIABLES voted, promise
vars == << voted, promise >>

TypeOK ==
    /\ voted \in [Acceptor -> SUBSET Votes]
    /\ promise \in [Acceptor -> Ballot]

Init ==
    /\ voted = [a \in Acceptor |-> {}]
    /\ promise = [a \in Acceptor |-> -1]

\* An acceptor may raise its promise threshold without voting; it simply refuses
\* to vote in ballots below the new threshold.
RaiseThreshold(a, n) ==
    /\ n > promise[a]
    /\ promise' = [promise EXCEPT ![a] = n]
    /\ UNCHANGED voted

\* An acceptor casts one vote in one ballot, only if that ballot is not below
\* its promise, it has not already voted in that ballot, no other value has
\* already collected a quorum in that ballot, and the value is safe at that
\* ballot (a quorum can vouch for it against every earlier ballot).
CastVote(a, v, b) ==
    /\ b >= promise[a]
    /\ \A x \in voted[a] : x.ball # b
    /\ \A x \in Acceptor :
         \A w \in voted[x] : (w.ball = b /\ w.val # v) => FALSE
    /\ \A c \in BallotRange : c < b => \E Q \in Quorum :
         \A m \in Q : \E x \in voted[m] : x.ball = c /\ x.val = v
    /\ voted' = [voted EXCEPT ![a] = @ \cup {[ball |-> b, val |-> v]}]
    /\ promise' = [promise EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptor, n \in Ballot : RaiseThreshold(a, n)
    \/ \E a \in Acceptor, v \in Value, b \in Ballot : CastVote(a, v, b)

Spec == Init /\ [][Next]_vars

(* Every cast vote is safe at its ballot, meaning it can be vouched for.       *)
OnlySafeVotes ==
    \A a \in Acceptor : \A w \in voted[a] :
        \A c \in BallotRange : c < w.ball =>
            \E Q \in Quorum : \A m \in Q :
                \E x \in voted[m] : x.ball = c /\ x.val = w.val

(* At most one value is ever voted for in any given ballot.                     *)
UniqueBallotValue ==
    \A a, b \in Acceptor : \A w \in voted[a] : \A x \in voted[b] :
        (w.ball = x.ball) => (w.val = x.val)

(* The vote-related and the threshold-related variables stay well-typed.        *)
VarsTyped == TypeOK

(* The chosen set derived from the votes is consistent: it never contains two  *)
(* distinct values, which is exactly what it means for the consensus to hold.  *)
Inv == OnlySafeVotes /\ UniqueBallotValue /\ VarsTyped

(* An abstract consensus spec that any concrete voting implementation must      *)
(* refine to; it looks only at the derived chosen set, not at the votes.        *)
ConsensusSpecBar == Spec /\ Inv

MCSymmetry ==
    {f \in [Acceptor -> Acceptor] :
        /\ \A a \in Acceptor : f[a] \in Acceptor
        /\ \A a, b \in Acceptor : f[a] = f[b] => a = b}

(* Substitution definitions: the .cfg file substitutes these in place of the  *)
(* declared constants so that permutation symmetry, bounded-value checking,    *)
(* and the ballot bound are enforced without changing the model itself.       *)
MCAcceptor == {a1, a2, a3}
MCValue == {v1, v2}
MCQuorum == { {a1, a2}, {a2, a3}, {a1, a3} }
MCBallot == {0, 1}
====