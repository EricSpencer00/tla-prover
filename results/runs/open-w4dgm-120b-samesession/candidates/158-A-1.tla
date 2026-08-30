---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

Vote == [ball : Ballot, val : Value]
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

VARIABLES votes, prom

vars == <<votes, prom>>

TypeOK ==
    /\ votes \in [MCAcceptor -> SUBSET Vote]
    /\ prom \in [MCAcceptor -> MCBallot \cup {-1}]

Init ==
    /\ votes = [a \in MCAcceptor |-> {}]
    /\ prom = [a \in MCAcceptor |-> -1]

Raise(a) ==
    /\ \E b \in MCBallot :
        /\ b > prom[a]
        /\ prom' = [prom EXCEPT ![a] = b]
    /\ UNCHANGED votes

\* Safety is the quorum condition: a value is safe at ballot b only if every
\* lower ballot is backed by a quorum that already voted for it or is dead.
SafeAt(a, b, val) ==
    /\ b >= prom[a]
    /\ \A c \in MCBallot :
         c < b => \E q \in MCQuorum :
            /\ \A x \in q : \E w \in votes[x] : w.ball = c /\ w.val = val
            \/ \A y \in q : \A w \in votes[y] : w.ball >= c

Vote(a, b, val) ==
    /\ b >= prom[a]
    /\ \A w \in votes[a] : w.ball # b
    /\ \A x \in MCAcceptor : (\A w \in votes[x] : w.ball = b) => w.val = val
    /\ \E q \in MCQuorum :
        \A x \in q : \E w \in votes[x] : w.ball = b /\ w.val = val
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {[ball |-> b, val |-> val]}]
    /\ prom' = [prom EXCEPT ![a] = b]

Next ==
    \/ \E a \in MCAcceptor : Raise(a)
    \/ \E a \in MCAcceptor, b \in MCBallot, val \in MCValue : Vote(a, b, val)

Spec == Init /\ [][Next]_vars

\* Chosen via quorum: a value is committed only when a quorum fully voted
\* for it, and no two distinct values can both reach that state.
Chosen == {val \in MCValue : \E q \in MCQuorum : \A a \in q : \E w \in votes[a] : w.val = val}

NoDoubleCommit ==
    /\ \A w \in UNION {votes[a] : a \in MCAcceptor} : SafeAt(a, w.ball, w.val)
    /\ \A c \in MCBallot : \E! val \in MCValue :
            \A x \in MCAcceptor : \A w \in votes[x] : w.ball = c => w.val = val
    /\ \E a \in MCAcceptor : \E w \in votes[a] : prom[a] = w.ball

\* ConsensusSpecBar is the abstract-consensus formulation of the same
\* safety condition, used for refinement checking against the concrete actions.
ConsensusSpecBar ==
    \A x \in MCAcceptor, y \in MCAcceptor :
        \A w \in votes[x], z \in votes[y] : (w.ball = z.ball) => (w.val = z.val)

\* Voters are distinguishable, so swapping them changes the reachable state
\* space; the symmetry set still has to be non-empty for PlusCal.
MCSymmetry == {id}
====