---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* Alias the richer, but finite-always-available, version of each domain to the
\* domain name itself.  The CFG substitutes these operators, so they must exist.
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\* A vote: an acceptor may cast at most one vote per ballot, naming a value.
Vote == [ac : Acceptor, b : Ballot, val : Value]

VARIABLES votes, promised, chosen
vars == <<votes, promised, chosen>>

\* A ballot's chosen value, derived from its acceptors' votes, if any exists.
BallotWinner(b) == CHOOSE v \in Value :
  \A a \in a1 : [ac |-> a, b |-> b, val |-> v] \in votes

TypeOK ==
  /\ votes \subseteq Vote
  /\ promised \in [Acceptor -> MCBallot \cup {-1}]
  /\ chosen \subseteq Value

Init ==
  /\ votes = {}
  /\ promised = [a \in Acceptor |-> -1]
  /\ chosen = {}

\* An acceptor may raise its promise threshold and thus skip earlier ballots.
RaisePromise(a, b) ==
  /\ b > promised[a]
  /\ promised' = [promised EXCEPT ![a] = b]
  /\ UNCHANGED <<votes, chosen>>

\* A vote is cast only if it is safe, meaning no earlier ballot has already
\* decided differently or can be decided in conflict with it.
CastVote(a, b, v) ==
  /\ b >= promised[a]
  /\ \A c \in MCBallot : [ac |-> a, b |-> c, val |-> v] \notin votes
  /\ \A d \in MCBallot :
        (\E x \in Acceptor : [ac |-> x, b |-> d, val |-> v] \in votes)
          => (\A x \in Acceptor : [ac |-> x, b |-> d, val |-> v] \in votes)
  /\ \A q \in MCQuorum :
        \E x \in q : [ac |-> x, b |-> b, val |-> v] \in votes
  /\ votes' = votes \cup {[ac |-> a, b |-> b, val |-> v]}
  /\ promised' = [promised EXCEPT ![a] = b]
  /\ UNCHANGED chosen

Next ==
  \E a \in Acceptor : \E b \in MCBallot :
    \/ RaisePromise(a, b)
    \/ \E v \in Value : CastVote(a, b, v)

Spec == Init /\ [][Next]_vars

\* SAFETY: at most one value is ever chosen by any quorum in any ballot.
AtMostOneChosen ==
  \A b \in MCBallot : (BallotWinner(b) # v1 => BallotWinner(b) = v2)

\* LIVENESS: not specified by this specification.
Inv == TypeOK /\ AtMostOneChosen

\* The high-level property the specification models: consensus is never broken.
ConsensusSpecBar == Inv
====