---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* The .cfg file substitutes the following operators for the constants when
\* instantiating the model.  They must be defined in the module.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

VARIABLES cast, thres

vars == <<cast, thres>>

Cast == [p: Acceptor, b: Ballot, v: Value]

\* An acceptor's votes in ballot b, collected as a set of values.
VotesAt(a, b) == { x.v : x \in { y \in cast : y.p = a /\ y.b = b } }

\* A quorum unanimously supporting v in ballot b.
QuorumFor(v, b) == { q \in Quorum : \A a \in q : b \in MCBallot => v \in VotesAt(a, b) }

\* A safe value has a supporting quorum at every lower ballot, so no different
\* value can have been chosen before it.
Safe(v, b) ==
  /\ \A c \in MCBBallot : c < b => QuorumFor(v, c) # {}
  /\ \A c \in MCBBallot : c < b => \A q \in Quorum :
        \A a \in q : (b \in MCBallot => v \in VotesAt(a, c))

TypeOK ==
  /\ cast \subseteq Cast
  /\ thres \in [Acceptor -> MCBallot \cup {-1}]

Init ==
  /\ cast = {}
  /\ thres = [a \in Acceptor |-> -1]

\* A promised acceptor may only vote in or above its current threshold; the
\* promise can also be raised without voting.
Raise(a, b) ==
  /\ b \in MCBallot
  /\ b > thres[a]
  /\ thres' = [thres EXCEPT ![a] = b]
  /\ UNCHANGED cast

Vote(a, b, v) ==
  /\ b \in MCBBallot
  /\ b >= thres[a]
  /\ \A x \in cast : ~(x.p = a /\ x.b = b)
  /\ \A x \in cast : ~(x.b = b /\ x.v # v)
  /\ Safe(v, b)
  /\ cast' = cast \cup {[p |-> a, b |-> b, v |-> v]}
  /\ thres' = [thres EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : Raise(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)

Spec == Init /\ [][Next]_vars

\* Consistency: the voting history names at most one chosen value.  It follows
\* from every vote being safe at its ballot and every ballot naming only one
\* value.
Inv ==
  /\ \A x \in cast : Safe(x.v, x.b)
  /\ \A a \in Acceptor, b \in Ballot :
       \A x \in cast : x.p = a /\ x.b = b => x.v = cast[b]
  /\ TypeOK

\* A refinement of the abstract consensus spec; the chosen set is derived from
\* the votes.
ConsensusSpecBar == ConsensusSpec(cast)

\* Any permutation of the acceptor set that leaves the ballot, value, and
\* quorum sets untouched is a symmetry of the model.
MCSymmetry == { f \in [Acceptor -> Acceptor] : \A q \in Quorum : f[q] \in Quorum }

====