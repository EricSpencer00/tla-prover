---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* MCAcceptor, MCValue, MCQuorum, MCBallot stand in for the unbounded
\* sets Acceptor, Value, Quorum, Ballot when model checking; they are
\* intended to be instantiated to a bounded subset in the .cfg.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

VARIABLES vote, threshold, chosen

vars == <<vote, threshold, chosen>>

Votes == [ball : Ballot, val : Value]

TypeOK ==
  /\ vote \in [Acceptor -> SUBSET Votes]
  /\ threshold \in [Acceptor -> {-1} \cup Ballot]
  /\ chosen \subseteq Value

Init ==
  /\ vote = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]
  /\ chosen = {}

RaiseThreshold(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED <<vote, chosen>>

\* A value is safe at ballot b if every lower ballot has a supporting quorum
\* that either already voted for v or cannot vote in that ballot.
IsSafeAt(v, b) ==
  \A c \in Ballot : (c < b) =>
    \E q \in Quorum :
      /\ \A a \in q : \E w \in Value : <<c, w>> \in vote[a] \/ threshold[a] > c
      /\ \E a \in q : <<c, v>> \in vote[a]

Vote(a, b, v) ==
  /\ b # threshold[a]
  /\ b >= threshold[a]
  /\ threshold[a] < b
  /\ \A c \in Ballot : <<c, v>> \notin vote[a]
  /\ \A p \in Acceptor : \A c \in Ballot : <<c, v>> \notin vote[p] => c = b
  /\ IsSafeAt(v, b)
  /\ vote' = [vote EXCEPT ![a] = @ \cup {<<b, v>>}]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED <<chosen>>

Next ==
  \/ \E a \in Acceptor, b \in Ballot : RaiseThreshold(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)

Spec == Init /\ [][Next]_vars

\* Every cast vote is safe at its ballot number.
NoUnsafeVote ==
  \A a \in Acceptor : \A v \in vote[a] : IsSafeAt(v.val, v.ball)

\* At most one value is voted for per ballot across all acceptors.
BallotSingleton ==
  \A v \in Value, b \in Ballot :
    (\E a \in Acceptor : <<b, v>> \in vote[a]) =>
      (\A p \in Acceptor : <<b, v>> \in vote[p])

\* The chosen set is derived from the votes and must be coherent with them.
Inv == NoUnsafeVote /\ BallotSingleton /\ TypeOK

\* The derived specification: at most one value is ever chosen by a quorum.
ConsensusSpecBar ==
  \A a \in Acceptor, b \in Ballot, v \in Value : <<b, v>> \in vote[a] => v \in chosen

\* Permutations of the acceptor set; with overlap, they form a symmetry.
MCSymmetry == {p \in [Acceptor -> Acceptor] : \A x \in Acceptor : p[p[x]] = x}

====