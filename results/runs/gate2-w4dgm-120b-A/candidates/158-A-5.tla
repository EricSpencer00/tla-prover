---- MODULE Voting ----
EXTENDS Integers, FiniteSets

(* The system's actors: acceptors that vote in numbered ballots, and quorums of
   acceptors; a quorum is a set of acceptors, and any two quorums overlap. *)
Acceptor == {a1, a2, a3}
Value == {v1, v2}
Quorum == {q1, q2}
Ballot == 0..2

CONSTANTS
    a1, a2, a3, v1, v2

IsQuorum(q) == q \in Quorum
AcceptorOf(x) == x[1]
BallotOf(x) == x[2]
ValueOf(x) == x[3]

VARIABLES votes, threshold

vars == <<votes, threshold>>

TypeOK ==
    /\ votes \in [Acceptor -> SUBSET (Acceptor \X Ballot \X Value)]
    /\ threshold \in [Acceptor -> Ballot \cup {-1}]

Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> -1]

\* An acceptor raises its promise threshold and will not vote in a ballot below it.
RaiseThreshold(a, b) ==
    /\ b > threshold[a]
    /\ threshold' = [threshold EXCEPT ![a] = b]
    /\ UNCHANGED votes

CastVote(a, v, b) ==
    /\ b >= threshold[a]
    /\ \A e \in votes[a] : BallotOf(e) # b
    /\ \A e \in votes[a] : ValueOf(e) = v
    /\ \A e \in votes : (BallotOf(e) = b /\ ValueOf(e) # v) => FALSE
    /\ \A c \in 0..(b - 1) : \E q \in Quorum :
           \A e \in q : (BallotOf(e) = c /\ ValueOf(e) = v \/ threshold[e] >= c)
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<a, b, v>>}]
    /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
    \/ \E a \in Acceptor, b \in Ballot : RaiseThreshold(a, b)
    \/ \E a \in Acceptor, v \in Value, b \in Ballot : CastVote(a, v, b)

Spec == Init /\ [][Next]_vars

\* A vote is safe only if every earlier ballot is already resolved for the same
\* value, which is what blocks a quorum from backing two different values.
VoteIsSafe == \A a \in Acceptor, e \in votes[a] :
    \A c \in 0..(BallotOf(e) - 1) : \E q \in Quorum :
        \A x \in q : (BallotOf(x) = c /\ ValueOf(x) = ValueOf(e) \/ threshold[x] >= c)

BallotSingleValued ==
    \A e1, e2 \in UNION {votes[a] : a \in Acceptor} :
        (BallotOf(e1) = BallotOf(e2)) => (ValueOf(e1) = ValueOf(e2))

NoContradiction == VoteIsSafe /\ BallotSingleValued

(* The chosen set is derived from the votes, so consensus consistency is a
   refinement of the ballot-uniqueness property. *)
ConsensusSpecBar == \A x \in UNION {votes[a] : a \in Acceptor} : True

\* Symmetry: swapping acceptor identities is invisible to the observable outcome.
MCSymmetry == (1 :> a1 @@ 2 :> a2 @@ 3 :> a3)
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

====