---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* Mapped to the finite sets used for model checking (e.g. {a1, a2, a3}).
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

VARIABLES votes, threshold

vars == <<votes, threshold>>

Vote == [ac : Acceptor, b : Ballot, val : Value]
CastBy(v) == { w \in votes : w.ac = v.ac }

TypeOK ==
  /\ votes \subseteq (Acceptor \X Ballot \X Value)
  /\ threshold \in [Acceptor -> (Ballot \cup {-1})]

BallotOf(v) == v[2]

\* Called IsSafe in the spec, but the proof writes it as a derived definition.
IsSafe(v) ==
  /\ \A c \in Ballot : c < BallotOf(v) =>
       \E Q \in MCQuorum :
         \A w \in Q : (\A e \in CastBy(w) : e.b >= c) \/ (\E e \in CastBy(w) : e.b = c /\ e.val = v.val)

Init ==
  /\ votes = {}
  /\ threshold = [a \in MCAcceptor |-> -1]

\* This is the "promise" part: an acceptor refuses to vote below its threshold.
RaiseThreshold(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

CastVote(a, b, val) ==
  /\ b >= threshold[a]
  /\ \A e \in CastBy(a) : e.b # b
  /\ \A e \in votes : (e.ac # a /\ e.b = b) => e.val = val
  /\ \E Q \in MCQuorum : IsSafe([ac |-> a, b |-> b, val |-> val])
  /\ votes' = votes \cup {[ac |-> a, b |-> b, val |-> val]}
  /\ threshold' = [threshold EXCEPT ![a] = b]

Contribute == \E a \in MCAcceptor, b \in MCBallot, val \in MCValue : CastVote(a, b, val)
RaiseAny == \E a \in MCAcceptor, b \in MCBallot : RaiseThreshold(a, b)

Next == Contribute \/ RaiseAny

Spec == Init /\ [][Next]_vars /\ WF_vars(RaiseAny) /\ SF_vars(Contribute)

Chosen == { val \in MCValue : \E Q \in MCQuorum : \A a \in Q : [ac |-> a, b |-> 0, val |-> val] \in votes }

Inv ==
  /\ \A e \in votes : IsSafe(e)
  /\ \A e1 \in votes, e2 \in votes : (e1.b = e2.b) => (e1.val = e2.val)
  /\ TypeOK

\* The refinement maps the chosen set to the values with a full quorum of votes.
ConsensusSpecBar == Chosen = { val \in MCValue : \E Q \in MCQuorum :
  \A a \in Q : \E e \in votes : e.ac = a /\ e.val = val }

\* Voters are symmetric, so swapping them in the global state is a self-loop.
MCSymmetry == [f \in [Acceptor -> MCAcceptor] |-> votes' = { [ac |-> f[e.ac], b |-> e.b, val |-> e.val] : e \in votes }]

====