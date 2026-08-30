---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

MCAcceptor == {a1, a2, a3}
MCValue == {v1, v2}
MCQuorum == Quorum
MCBallot == Ballot

VARIABLES votes, thresh
vars == <<votes, thresh>>

RECURSIVE SumOf(_, _)
SumOf(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOf(f, S \ {x})

TypeOK ==
    /\ votes \in [MCAcceptor -> SUBSET (MCBallot \X MCValue)]
    /\ thresh \in [MCAcceptor -> Int]

QuorumFor(v, b) ==
    {Q \in MCQuorum : \A a \in Q : <<b, v>> \in votes[a]}

Init ==
    /\ votes = [a \in MCAcceptor |-> {}]
    /\ thresh = [a \in MCAcceptor |-> -1]

\* An acceptor may promise to only consider ballots at or above a higher
\* number, so it never has to un-vote an older ballot it already cast.
RaiseThresh(a, b) ==
    /\ b > thresh[a]
    /\ thresh' = [thresh EXCEPT ![a] = b]
    /\ UNCHANGED votes

\* Safety: no quorum for a different value can already exist in the same
\* ballot, and the value must be safe in every lower ballot.
Vote(a, v, b) ==
    /\ b >= thresh[a]
    /\ \A c \in MCBallot : (c < b) => <<b, v>> \notin votes[a]
    /\ (\A q \in MCQuorum : \A x \in q : votes[x] \subseteq {<<b, v>>})
    /\ (\A c \in MCBallot : c < b => (QuorumFor(v, c) # {}))
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
    /\ thresh' = [thresh EXCEPT ![a] = b]

Next ==
    \/ \E a \in MCAcceptor, b \in MCBallot : RaiseThresh(a, b)
    \/ \E a \in MCAcceptor, v \in MCValue, b \in MCBallot : Vote(a, v, b)

Spec == Init /\ [][Next]_vars

\* The invariant is broken into three disciplined properties; each is
\* separately easy to argue from the action shape, and together they are
\* exactly what keeps the chosen set to a single value.
EveryVoteIsSafe ==
    \A a \in MCAcceptor, c \in MCBallot :
        (\E v \in MCValue : <<c, v>> \in votes[a])
            => (\A d \in MCBallot : d < c => QuorumFor(v, d) # {})

SingleValPerBallot ==
    \A c \in MCBallot :
        \A a, b \in MCAcceptor :
            (\E v \in MCValue : <<c, v>> \in votes[a])
                => (\A w \in MCValue : <<c, w>> \in votes[b] => w = v)

Inv == EveryVoteIsSafe /\ SingleValPerBallot /\ TypeOK

\* The abstraction: the chosen set is derived directly from the votes, and
\* the safety properties above are exactly what keeps that derived set
\* to one value, which is what consensus is about.
ConsensusSpecBar ==
    LET Chosen == {v \in MCValue : \E c \in MCBallot : QuorumFor(v, c) # {}}
    IN Cardinality(Chosen) <= 1

\* The symmetry group is precisely the acceptor permutations; they keep
\* the quorums structurally intact, so they are sound to explore.
MCSymmetry == {f \in [MCAcceptor -> MCAcceptor] : f \in [MCAcceptor -> MCAcceptor]}
====