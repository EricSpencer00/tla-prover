---- MODULE Voting ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* Mapped constants: the cfg overrides these with concrete finite instances.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

VARIABLES votes, threshold

TypeOK ==
  /\ votes \in [MCAcceptor -> SUBSET (MCBallot \X MCValue)]
  /\ threshold \in [MCAcceptor -> MCBallot \cup {-1}]

Init ==
  /\ votes = [a \in MCAcceptor |-> {}]
  /\ threshold = [a \in MCAcceptor |-> -1]

\* A quorum in which every member has voted for v at ballot c, or can never vote at c.
QuorumSupports(v, c) ==
  \E Q \in MCQuorum :
    /\ Q \subseteq MCAcceptor
    /\ \A a \in Q : <<c, v>> \in votes[a]
    /\ \A b \in MCBallot : b < c => \E a \in Q : <<b, v>> \in votes[a]

SafeAt(v, b) ==
  /\ (\A c \in MCBallot : c < b => QuorumSupports(v, c)
  /\ (\A a \in MCAcceptor : <<b, v>> \notin votes[a]

\* Safety requires overlap of any two quorums, which is what prevents a second
\* value from being backed in a later ballot once an earlier one quorum-backed.
\* (Formally: no two disjoint quorums voting the same ballot.)
QuorumsOverlap == \A Q1, Q2 \in MCQuorum : Q1 \subseteq MCAcceptor /\ Q2 \subseteq MCAcceptor => Q1 \cap Q2 # {}

Vote(a, v, b) ==
  /\ b >= threshold[a]
  /\ \A c \in MCBallot : <<c, v>> \notin votes[a]
  /\ (\A c \in MCBallot, w \in MCValue : c = b /\ w # v => <<c, w>> \notin votes[a])
  /\ QuorumSupports(v, b)
  /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

RaiseThreshold(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

Next ==
  \/ \E a \in MCAcceptor, v \in MCValue, b \in MCBallot : Vote(a, v, b)
  \/ \E a \in MCAcceptor, b \in MCBallot : RaiseThreshold(a, b)

Spec == Init /\ [][Next]_<<votes, threshold>>

ChosenValues == {v \in MCValue : \E Q \in MCQuorum :
  Q \subseteq MCAcceptor /\ \A a \in Q : \E b \in MCBallot : <<b, v>> \in votes[a]}

Inv ==
  /\ \A v \in MCValue, b \in MCBallot : (\A a \in MCAcceptor : <<b, v>> \in votes[a]) => SafeAt(v, b)
  /\ \A v1, v2 \in MCValue, b \in MCBallot :
        (\A a \in MCAcceptor : <<b, v1>> \in votes[a]) /\ (\A a \in MCAcceptor : <<b, v2>> \in votes[a]) => v1 = v2
  /\ QuorumsOverlap

\* The reduction: the chosen set is derived from the vote set, so the chosen
\* set is never larger than the vote set and inherits the at-most-one-value
\* property from the vote-level per-ballot check.
ConsensusSpecBar == Cardinality(ChosenValues) <= 1

\* Permuting the acceptors is a symmetry of the model; each permutation of the
\* acceptor set is a bijection lifted pointwise to the vote records.
MCSymmetry ==
  {f \in [MCAcceptor -> MCAcceptor] :
     /\ \A a \in MCAcceptor : f[a] \in MCAcceptor
     /\ \A x, y \in MCAcceptor : f[x] = f[y] => x = y}

====