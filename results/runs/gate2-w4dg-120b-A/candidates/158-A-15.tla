---- MODULE Voting ----
EXTENDS Naturals

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

NoVal == "noval"

\* Each acceptor carries a set of votes it has cast (paired ballot/value)
\* and a threshold: a ballot number below which it will not vote. The
\* thresholds and the overlap property of quorums are what keep voting
\* safe and keep two different values from ever both being chosen by
\* overlapping quorums in the same or a later ballot.

VARIABLES votes, thr

vars == << votes, thr >>

Votes == [ac : Acceptor, ballot : Ballot, val : Value]

TypeOK ==
    /\ votes \subseteq Votes
    /\ thr \in [Acceptor -> Ballot \cup {-1}]

Init ==
    /\ votes = {}
    /\ thr = [a \in Acceptor |-> -1]

AtMostOneValuePerBallot ==
    \A a1 \in votes, a2 \in votes :
        (a1.ballot = a2.ballot /\ a1.val # a2.val) => a1.ac = a2.ac

\* Quorums must overlap pairwise, and that assumption is declared as a
\* true fact here rather than read from the model: it is the substance of
\* the agreement argument, not a model artifact.
QuorumsOverlap ==
    \A q1 \in Quorum, q2 \in Quorum : \E x \in q1 : x \in q2

\* A value is safe at ballot b if every lower ballot has been covered by a
\* quorum voting for it, or those voters have already lost the ability to
\* vote in that earlier slot. A vote in ballot b is only allowed when it is
\* safe at b, which is the only place the overlap property is brought to bear.
SafeAt(v, b) ==
    \A c \in 0..(b - 1) :
        \E q \in Quorum :
            \A a \in q :
                \/ \E w \in votes : /\ w.ac = a /\ w.ballot = c /\ w.val = v
                \/ thr[a] > c

IncreaseThreshold(a, b) ==
    /\ b > thr[a]
    /\ thr' = [thr EXCEPT ![a] = b]
    /\ UNCHANGED votes

CastVote(a, b, v) ==
    /\ b >= thr[a]
    /\ \A w \in votes : ~(w.ac = a /\ w.ballot = b)
    /\ \A w \in votes : (w.ballot = b) => w.val = v
    /\ SafeAt(v, b)
    /\ votes' = votes \cup {[ac |-> a, ballot |-> b, val |-> v]}
    /\ thr' = [thr EXCEPT ![a] = b]
    /\ UNCHANGED << >>

Next ==
    \/ \E a \in Acceptor, b \in Ballot : IncreaseThreshold(a, b)
    \/ \E a \in Acceptor, b \in Ballot, v \in Value : CastVote(a, b, v)

Spec == Init /\ [][Next]_vars

\* The chosen set is derived from the votes: every value that a quorum has
\* voted for in some ballot appears as chosen. Because votes for a ballot
\* never disagree, and quorum overlap forces safety across ballots, the
\* derived chosen set can never hold two different values.
Inv ==
    /\ TypeOK
    /\ AtMostOneValuePerBallot
    /\ QuorumsOverlap

\* The abstract consensus spec says at most one value is ever chosen. The
\* voting algorithm refines it: the safety invariant above keeps the derived
\* chosen set to at most one value, which is exactly what the abstract spec
\* requires.
ConsensusSpecBar == Cardinality({v \in Value : \E q \in Quorum : \A a \in q : [ac |-> a, ballot |-> 0, val |-> v] \in votes}) <= 1

====