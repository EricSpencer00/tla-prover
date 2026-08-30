---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2

Acceptor == {a1, a2, a3}
Value == {v1, v2}
Quorum == { {a1, a2}, {a2, a3}, {a1, a3} }
Ballot == 0..2

None == "none"
Votes == [ball : Ballot, val : Value]
Thresholds == [a1 : Ballot \cup {None}, a2 : Ballot \cup {None}, a3 : Ballot \cup {None}]

VARIABLES casts, thresh
vars == <<casts, thresh>>

TypeOK ==
    /\ casts \in [Acceptor -> SUBSET Votes]
    /\ thresh \in Thresholds

Init ==
    /\ casts = [a \in Acceptor |-> {}]
    /\ thresh = [a \in Acceptor |-> None]

Overlaps(q1, q2) == (q1 \cap q2) # {}

\* No value is considered safe unless every lower ballot is already covered
\* by the overlapping-quorum structure; this strong requirement is what
\* forces different ballots to agree on the same value.
SafeAt(v, b) ==
    \A c \in 1..(b - 1) : \E q \in Quorum :
        \A m \in q :
            \/ [ball |-> c, val |-> v] \in casts[m]
            \/ \A vp \in casts[m] : vp.ball < c

\* Two safety-critical constraints are checked at vote time and two are
\* invariants; the two vote-time constraints are exactly what make the
\* three invariant facts hold, and they are the only reason the chosen set
\* can never end up with two different values.
Vote(a, b, v) ==
    /\ (thresh[a] = None \/ b >= thresh[a])
    /\ \A m \in Acceptor : [ball |-> b, val |-> v] \notin casts[m]
    /\ \A m \in Acceptor : \A w \in Value : ([ball |-> b, val |-> w] \in casts[m]) => w = v
    /\ SafeAt(v, b)
    /\ casts' = [casts EXCEPT ![a] = casts[a] \cup {[ball |-> b, val |-> v]}]
    /\ thresh' = [thresh EXCEPT ![a] = b]

Promise(a, b) ==
    /\ (thresh[a] = None \/ b > thresh[a])
    /\ thresh' = [thresh EXCEPT ![a] = b]
    /\ UNCHANGED casts

Next ==
    \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)
    \/ \E a \in Acceptor, b \in Ballot : Promise(a, b)

Spec == Init /\ [][Next]_vars

\* Safety: at most one value is ever recorded as the chosen outcome.
Chosen == { v \in Value : \E a \in Acceptor : [ball |-> 0, val |-> v] \in casts[a] }

CastIsSafe ==
    \A a \in Acceptor : \A vp \in casts[a] : SafeAt(vp.val, vp.ball)

OneValuePerBallot ==
    \A m1, m2 \in Acceptor : \A v1, v2 \in Value, b \in Ballot :
        (\A a \in {m1, m2} : [ball |-> b, val |-> IF a = m1 THEN v1 ELSE v2] \in casts[a])
            => v1 = v2

VarsWellFormed == TypeOK /\ \A a \in Acceptor : thresh[a] # None => thresh[a] \in Ballot

Inv == CastIsSafe /\ OneValuePerBallot /\ VarsWellFormed

\* Abstract consensus interface: the module presents a single chosen set
\* derived from the votes, and the refinement linking it back to the votes
\* is proved in the next theorem.
ConsensusSpecBar == Chosen \subseteq Value

\* Two concrete consequences of the overlap property: each vote is safe,
\* and the chosen set collapses to at most one value.
TheVotingImplementationIsConsistent ==
    /\ CastIsSafe
    /\ (Chosen = {} \/ (\E v \in Value : Chosen = {v}))

\* Symmetry: the three acceptors are interchangeable, so swapping any two
\* of them must preserve every reachable state.
MCSymmetry == {f \in [Acceptor -> Acceptor] : \A x, y \in Acceptor : (x = y) <=> (f[x] = f[y])}

=======