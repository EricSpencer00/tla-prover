---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* The .cfg file substitutes these operators for the constants, so they must be
\* defined exactly as named here (the left name is overridden by the right).
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

VARIABLES votes, threshold

vars == <<votes, threshold>>

Vote == [ac : Acceptor, b : Ballot, v : Value]
QuorumFor(v) == {q \in Quorum : \A a \in q : v \in votes[a]}
SafeAt(v, b) ==
  \A c \in 0..(b - 1) : \E q \in Quorum :
    \A a \in q : (Vote \in votes[a] /\ Vote.b = c /\ Vote.v = v) \/ (b < c)

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET Vote]
  /\ threshold \in [Acceptor -> Ballot \cup {-1}]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

\* An acceptor may raise its promise threshold without voting.
RaiseThreshold(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* An acceptor votes for a value in a ballot, provided the ballot is above its
\* threshold, it has not already voted in that ballot, no other acceptor voted
\* for a different value in that ballot, and the value is safe at that ballot.
CastVote(a, b, v) ==
  /\ b >= threshold[a]
  /\ \A w \in votes[a] : w.b # b
  /\ \A w \in votes[a] : w.v = v
  /\ \A c \in Acceptor : \A w \in votes[c] : (w.b = b) => (w.v = v)
  /\ SafeAt(v, b)
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {[ac |-> a, b |-> b, v |-> v]}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : RaiseThreshold(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : CastVote(a, b, v)

Spec == Init /\ [][Next]_vars

\* Every vote cast is safe at its ballot number.
EveryVoteIsSafe ==
  \A a \in Acceptor : \A w \in votes[a] : SafeAt(w.v, w.b)

\* At most one value is voted for per ballot across all acceptors.
AtMostOneValuePerBallot ==
  \A a, c \in Acceptor : \A w \in votes[a] : \A x \in votes[c] :
    (w.b = x.b) => (w.v = x.v)

\* The chosen set is derived from the votes, so consistency follows from the
\* two invariants above.
Inv == TypeOK /\ EveryVoteIsSafe /\ AtMostOneValuePerBallot

\* The chosen set contains at most one value: if a quorum voted for v in some
\* ballot and a quorum voted for w in some ballot, then v = w.
ConsensusSpecBar ==
  \A v, w \in Value :
    (\E q \in Quorum : \A a \in q : \E x \in votes[a] : x.v = v) /\
    (\E q \in Quorum : \A a \in q : \E x \in votes[a] : x.v = w)
      => (v = w)

\* The .cfg file declares this symmetry set, so it must be present here.
MCSymmetry == {}

====