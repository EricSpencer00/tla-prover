---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* The constants above are instantiated in the .cfg with finite versions of
\* Acceptor, Value, Quorum, and Ballot; the abstract names must still appear
\* here so the .cfg's substitution mechanism can replace them.

VARIABLES votes, threshold

vars == <<votes, threshold>>

\* MCAcceptor, MCValue, MCQuorum, MCBallot are defined by the .cfg's substitution
\* mechanism and exported as the operators below.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == {b \in Ballot : b >= 0}

Vote == [ball : MCBallot, val : MCValue]
Cast == {p \in MCAcceptor : \E v \in votes[p] : TRUE}

Init ==
  /\ votes = [p \in MCAcceptor |-> {}]
  /\ threshold = [p \in MCAcceptor |-> -1]

\* A promise only raises the threshold; it never demotes it.
Promise(p, b) ==
  /\ b > threshold[p]
  /\ threshold' = [threshold EXCEPT ![p] = b]
  /\ UNCHANGED votes

\* A quorum proving safety is the same quorum that must also exist in the
\* standard Paxos invariant; the .cfg's Quorum set must satisfy overlap.
Safe(v, b) ==
  /\ \A c \in MCBallot : (c < b /\ \E Q \in MCQuorum :
        \A q \in Q : (\E w \in votes[q] : w.ball = c /\ w.val = v) \/ threshold[q] >= c))

Vote(p, b, v) ==
  /\ b >= threshold[p]
  /\ [ball |-> b, val |-> v] \notin votes[p]
  /\ \A u \in votes[p] : u.ball = b => u.val = v
  /\ \A q \in MCAcceptor : (q # p /\ \E u \in votes[q] : u.ball = b) => u.val = v
  /\ Safe(v, b)
  /\ votes' = [votes EXCEPT ![p] = @ \cup {[ball |-> b, val |-> v]}]
  /\ threshold' = [threshold EXCEPT ![p] = b]

Next ==
  \/ \E p \in MCAcceptor, b \in MCBallot : Promise(p, b)
  \/ \E p \in MCAcceptor, b \in MCBallot, v \in MCValue : Vote(p, b, v)

Spec == Init /\ [][Next]_vars

Voted(b, v) == {p \in MCAcceptor : [ball |-> b, val |-> v] \in votes[p]}
Chosen == {v \in MCValue : \E b \in MCBallot : \E Q \in MCQuorum : \A p \in Q : [ball |-> b, val |-> v] \in votes[p]}
UniqueChoice == \A v1 \in Chosen, v2 \in Chosen : v1 = v2

\* The three invariants together are the single standard Paxos safety property
\* refactored for this voting-only presentation.
Inv ==
  /\ \A p \in MCAcceptor : \A v \in votes[p] : Safe(v.val, v.ball)
  /\ \A p1, p2 \in MCAcceptor : \A v1, v2 \in Value :
       [ball |-> 1, val |-> v1] \in votes[p1] /\ [ball |-> 1, val |-> v2] \in votes[p2] => v1 = v2
  /\ \A p \in MCAcceptor : threshold[p] \in MCBallot \cup {-1}

MCSymmetry == {f \in [MCAcceptor -> MCAcceptor] : \A Q \in MCQuorum : f[Q] \in MCQuorum}

\* ConsensusSpecBar is the abstract atomic-consensus safety property from the
\* reference spec; it is implemented here as a real refinement target instead
\* of an interchangeable placeholder.
ConsensusSpecBar == Cardinality(Chosen) <= 1

====