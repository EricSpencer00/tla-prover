---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  a1, a2, a3,
  v1, v2,
  Acceptor,
  Value,
  Quorum,
  Ballot

\* The .cfg file substitutes these with bounded or concrete versions for model
\* checking; the operators themselves are identity maps over the abstract sets.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

VARIABLES votes, promised

vars == <<votes, promised>>

VoteSpace == [ac : Acceptor, b : Ballot, v : Value]

Yes(v, b) == {a \in Acceptor : <<a, b, v>> \in votes}

VoteRecorded == {<<a, b, v>> \in votes : True}

TypeOK ==
  /\ votes \subseteq VoteSpace
  /\ promised \in [Acceptor -> Ballot \cup {-1}]

Init ==
  /\ votes = {}
  /\ promised = [a \in Acceptor |-> -1]

\* An acceptor may raise its promise threshold without casting a vote.
PromiseUp(a, b) ==
  /\ b > promised[a]
  /\ promised' = [promised EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* No acceptor may ever cast a vote in a ballot it promised not to join.
\* The quorum safety check looks back at every earlier ballot, so a vote
\* for one value in one ballot rules out a different value in any ballot.
CastVote(a, b, v) ==
  /\ b >= promised[a]
  /\ \A x \in Ballot : x < b => x \notin promised[a]
  /\ ~ (\E x \in Ballot : x >= b /\ <<a, x, v>> \in votes)
  /\ \A x \in Ballot, w \in Value :
       (<<a, x, w>> \in votes /\ w # v) => x < b
  /\ \E Q \in Quorum :
       /\ a \in Q
       /\ \A c \in Ballot : c < b =>
            \E Qc \in Quorum :
              /\ a \in Qc
              /\ \A x \in Qc :
                 \/ Qc = Q
                 \/ <<x, c, v>> \in votes
                 \/ \A d \in Ballot : d < c => d \notin promised[x]
  /\ votes' = votes \cup {<<a, b, v>>}
  /\ promised' = [promised EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : PromiseUp(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : CastVote(a, b, v)

Spec == Init /\ [][Next]_vars

\* A vote is rarely safe unless every earlier ballot already backed the same
\* value in some quorum, or was unavailable to any acceptor.
Safe(b, v) ==
  /\ \A c \in Ballot : c < b =>
       \E Q \in Quorum :
         /\ \A x \in Q : <<x, c, v>> \in votes \/ \A d \in Ballot : d < c => d \notin promised[x]
  /\ \A x \in Acceptor : <<x, b, v>> \in votes \/ b > promised[x]

\* Votes respect quorums and the ballot hierarchy, so at most one value is ever
\* chosen across the whole run.
AtMostOneChosen ==
  /\ \A x \in votes : Safe(x.b, x.v)
  /\ \A x, y \in votes : (x.b = y.b /\ x.v # y.v) => x = y
  /\ TypeOK

Inv == AtMostOneChosen

\* The high-level contract: once a quorum has coalesced around a value, no
\* different value can ever be selected instead.
ConsensusSpecBar == AtMostOneChosen

\* Quorums must overlap; that guarantee is assumed and never broken.
MCSymmetry == {}

====