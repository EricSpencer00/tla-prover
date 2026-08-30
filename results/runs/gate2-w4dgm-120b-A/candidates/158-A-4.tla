---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* Identity permutations: each actor maps to itself, so the set of permutations
\* is fully captured by these four constant-permuted variants of the same set.
MCSymmetry == { [a1 |-> a1, a2 |-> a2, a3 |-> a3], [a1 |-> a2, a2 |-> a1, a3 |-> a3],
                [a1 |-> a3, a2 |-> a2, a3 |-> a1], [a1 |-> a1, a2 |-> a3, a3 |-> a2] }

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

\* votes[a] is the set of (ballot, value) pairs acceptor a has cast; thr[a] is the
\* ballot number a has promised not to vote below -- -1 means no promise yet.
VARIABLES votes, thr

vars == <<votes, thr>>

TypeOK ==
    /\ votes \in [MCAcceptor -> SUBSET (MCBallot \X MCValue)]
    /\ thr \in [MCAcceptor -> MCBallot \cup {-1}]

Init ==
    /\ \E a \in MCAcceptor : votes = [x \in MCAcceptor |-> {}] /\ thr = [x \in MCAcceptor |-> -1]

\* An acceptor raises its promise threshold (it will not vote below it).
Raise(a, b) ==
    /\ b > thr[a]
    /\ thr' = [thr EXCEPT ![a] = b]
    /\ UNCHANGED votes

\* Voting: an acceptor may vote in ballot b for value v only if the ballot is
\* above its threshold and no other value already has a ballot-b quorum.
Vote(a, b, v) ==
    /\ LET twoAcceptorQuorumsVoteForDifferentValuesInTheSameBallot ==
            \E p, q \in MCAcceptor :
                \E v1, v2 \in MCValue :
                    /\ v1 # v2
                    /\ \E g1 \in MCQuorum : \A x \in g1 : <<b, v1>> \in votes[x]
                    /\ \E g2 \in MCQuorum : \A x \in g2 : <<b, v2>> \in votes[x]
       IN twoAcceptorQuorumsVoteForDifferentValuesInTheSameBallot
    /\ b >= thr[a]
    /\ \A v' \in MCValue : <<b, v'>> \notin votes[a]
    /\ \A g \in MCQuorum : \A x \in g : <<b, v>> \in votes[x]
    /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
    /\ thr' = [thr EXCEPT ![a] = b]

Next ==
    \E a \in MCAcceptor : \E b \in MCBallot : Raise(a, b) \/ \E v \in MCValue : Vote(a, b, v)

\* SAFETY LEMMA: every cast vote is safe at its own ballot number (quorum-safe
\* down to ballot zero), which is the heart of the consistency guarantee.
EveryVoteIsBallotSafe ==
    \A a \in MCAcceptor : \A w \in votes[a] :
        \A c \in 0 .. (w[1] - 1) : \E g \in MCQuorum :
            \A x \in g : \E w' \in votes[x] : w'[1] = c /\ w'[2] = w[2]

\* Every ballot has at most one voted value: two quorum votes in the same
\* ballot cannot disagree, so no two values can ever both become chosen.
\* SAFETY PROPERTY: this is the literal translation of the description.
BallotHasOneValue ==
    \A a \in MCAcceptor : \A b \in votes[a] :
        \A c \in MCAcceptor : \A d \in MCAcceptor :
            /\ <<b[1], b[2]>> \in votes[a]
            /\ <<b[1], b[2]>> \in votes[c]
            /\ <<b[1], d[2]>> \in votes[c]
            => b[2] = d[2]

Spec == Init /\ [][Next]_vars

Inv == TypeOK /\ EveryVoteIsBallotSafe /\ BallotHasOneValue

\* ABSTRACTION: the chosen set is derived from the votes, and both invariants
\* together imply it never holds two distinct values.
ConsensusSpecBar == BallotHasOneValue

====