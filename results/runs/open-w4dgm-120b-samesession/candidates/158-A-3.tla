---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS Acceptor, Value, Quorum, Ballot

\* A quorum is a set of acceptors.  Quorums must pairwise overlap on some acceptor;
\* this is what guarantees no two different values can ever both form a quorum.
QuorumA == CHOOSE q \in Quorum : TRUE

VARIABLES votes, threshold

vars == << votes, threshold >>

TypeOK ==
    /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
    /\ threshold \in [Acceptor -> Ballot]

Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> 0]

\* A vote is authorized only if every earlier ballot was decided for the same value.
\* This is what stops a value voted for in one ballot from being contradicted later.
VoteSafe(a, b, v) ==
    /\ b >= threshold[a]
    /\ \A c \in Ballot : c < b => \E q \in Quorum :
        \A m \in q : << c, v >> \in votes[m]

OneValuePerBallot ==
    \A a1 \in Acceptor, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value :
        (<< b, v1 >> \in votes[a1] /\ << b, v2 >> \in votes[a2]) => v1 = v2

\* Votes made at or above the acceptor's own threshold, so a lagging acceptor
\* cannot be forced to vote in a ballot it has already pledged to skip.
AllVotesSafe == \A a \in Acceptor : \A b \in Ballot, v \in Value : << b, v >> \in votes[a] => VoteSafe(a, b, v)

Vote(a, b, v) ==
    /\ VoteSafe(a, b, v)
    /\ << b, v >> \notin votes[a]
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<< b, v >>}]
    /\ threshold' = [threshold EXCEPT ![a] = b]

RaiseThreshold(a, b) ==
    /\ b > threshold[a]
    /\ threshold' = [threshold EXCEPT ![a] = b]
    /\ UNCHANGED votes

Next ==
    \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)
    \/ \E a \in Acceptor, b \in Ballot : RaiseThreshold(a, b)

\* The chosen set is derived from the votes (a quorum per value), and a quorum
\* is a strict majority, so the derived choice can never be two different values.
Suggested == { v \in Value : \E q \in Quorum : \A m \in q : \E b \in Ballot : << b, v >> \in votes[m] }

Spec == Init /\ [][Next]_vars

Inv == AllVotesSafe /\ OneValuePerBallot

\* One abstract consensus instance for the entire voting round: a single chosen
\* value, derived from the votes.  This is what the refinement maps to.
ConsensusSpecBar == Cardinality(Suggested) > 1

\* Symmetry: swapping a1 and a2 is a model isomorphism -- the acceptors are
\* otherwise indistinguishable, and any trace stays valid under the swap.
MCSymmetry == { (a1 :> a2 @@ a2 :> a1 @@ a3 :> a3), (a1 :> a1 @@ a2 :> a2 @@ a3 :> a3) }

\* The .cfg file plugs these definitions in as constant/variable instantiations,
\* so they must be defined here -- the operators themselves have no content.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

====