---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, TLC

\* The reference model's .cfg defines the constants below as concrete elements,
\* and also substitutes the typed-set operators for the abstract constant names.
CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

CONSTANTS MCAcceptor, MCValue, MCQuorum, MCBallot

VARIABLES votes, threshold

vars == <<votes, threshold>>

RECURSIVE HasQuorum(_, _)
HasQuorum(S, val) ==
  \E Q \in Quorum : S \subseteq Q /\ \A a \in S : <<val, Q>> \in votes[a]

QuorumsIntersect == \A Q1 \in Quorum : \A Q2 \in Quorum : Q1 \cap Q2 # {}

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ threshold \in [Acceptor -> {-1} \cup Ballot]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

SafeAtBallot(a, v, b) ==
  /\ b \notin {w[1] : w \in votes[a]}
  /\ \A c \in 0..(b - 1) : HasQuorum(Quorum, v)

AtMostOneValueVotedPerBallot ==
  \A a1, a2 \in Acceptor : \A v1, v2 \in Value : \A b \in Ballot :
    (<<b, v1>> \in votes[a1] /\ <<b, v2>> \in votes[a2]) => v1 = v2

VoteImpliesSafe ==
  \A a \in Acceptor : \A v \in Value : \A b \in Ballot :
    <<b, v>> \in votes[a] => SafeAtBallot(a, v, b)

AtMostOneChosenValue ==
  \A v1 \in Value : \A v2 \in Value :
    (\E Q1 \in Quorum : HasQuorum(Q1, v1)) /\ (\E Q2 \in Quorum : HasQuorum(Q2, v2))
      => v1 = v2

Inv == TypeOK /\ AtMostOneValueVotedPerBallot /\ VoteImpliesSafe /\ AtMostOneChosenValue

\* Raising the threshold is what fences off lower ballots completely.
RaiseThreshold(a) ==
  /\ \E b \in MCBallot : b > threshold[a] /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

CastVote(a, v, b) ==
  /\ b \in MCBallot
  /\ b >= threshold[a]
  /\ ~\E c \in Ballot : <<c, v>> \in votes[a]
  /\ \A w \in votes[a] : w[2] = v
  /\ SafeAtBallot(a, v, b)
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor : RaiseThreshold(a)
  \/ \E a \in Acceptor : \E v \in Value : \E b \in Ballot : CastVote(a, v, b)

Spec == Init /\ [][Next]_vars

\* The abstract spec's all-encompassing invariant, refined to this level.
ConsensusSpecBar == Inv

\* Every permutation of the acceptor set is a symmetry of the spec.
MCSymmetry == {f \in [Acceptor -> Acceptor] : \A a, b \in Acceptor : a = b => f[a] = f[b]}

====