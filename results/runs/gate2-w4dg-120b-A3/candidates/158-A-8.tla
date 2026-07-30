---- MODULE Voting ----
EXTENDS Integers, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

ASSUME MCAcceptor \subseteq Acceptor
ASSUME MCValue \subseteq Value
ASSUME MCQuorum \subseteq Quorum
ASSUME MCBallot \subseteq Ballot

VARIABLES vote, minBallot

vars == <<vote, minBallot>>

TypeOK ==
    /\ vote \in [Acceptor -> SUBSET (Ballot \X Value)]
    /\ minBallot \in [Acceptor -> Ballot \cup {-1}]

Init ==
    /\ vote = [p \in Acceptor |-> {}]
    /\ minBallot = [p \in Acceptor |-> -1]

\* A quorum of acceptors has all voted for a given value in a given ballot.
AgreedFor(v, b) ==
    \E Q \in Quorum : \A p \in Q : <<b, v>> \in vote[p]

\* A quorum of acceptors would not vote for any value other than v in ballot b.
SafeAt(v, b) ==
    \A c \in {x \in Ballot : x < b} :
        \E Q \in Quorum :
            \A p \in Q :
                \/ <<c, v>> \in vote[p]
                \/ \A z \in Value : <<c, z>> \notin vote[p]

\* An acceptor pledges to not vote below ballot b, without actually voting.
RaiseMin(p, b) ==
    /\ b > minBallot[p]
    /\ minBallot' = [minBallot EXCEPT ![p] = b]
    /\ UNCHANGED vote

\* An acceptor votes, but only on a strictly safe value and ballot.
CastVote(p, v, b) ==
    /\ b >= minBallot[p]
    /\ \A q \in Acceptor : <<b, v>> \notin vote[q]
    /\ \A q \in Acceptor : ~(\E z \in Value : z # v /\ <<b, z>> \in vote[q])
    /\ SafeAt(v, b)
    /\ vote' = [vote EXCEPT ![p] = @ \cup {<<b, v>>}]
    /\ minBallot' = [minBallot EXCEPT ![p] = b]

Next ==
    \E p \in Acceptor :
        \/ \E b \in Ballot : RaiseMin(p, b)
        \/ \E v \in Value, b \in Ballot : CastVote(p, v, b)

Spec == Init /\ [][Next]_vars

\* Every cast vote is safe at its ballot number.
InvVoterSafety == \A p \in Acceptor : \A e \in vote[p] : SafeAt(e[2], e[1])

\* Two quorums never endorse two different values in the same ballot.
InvSingleChoicePerBallot == \A b \in Ballot : \A v \in Value : AgreedFor(v, b) => ~(\E w \in Value : w # v /\ AgreedFor(w, b))

\* Correctness of the types used throughout.
InvTypeOK == TypeOK

Inv == InvVoterSafety /\ InvSingleChoicePerBallot /\ InvTypeOK

\* The chosen set is empty or a single value, so the algorithm has reached a
\* consensus. It is derived from the votes to show the refinement.
Chosen == {v \in Value : \E b \in Ballot : AgreedFor(v, b)}
ConsensusSpecBar == Cardinality(Chosen) <= 1

MCSymmetry ==
    {f \in [Acceptor -> Acceptor] :
        /\ f``MCAcceptor = MCAcceptor
        /\ \A Q \in MCQuorum : f[Q] \in MCQuorum}

====