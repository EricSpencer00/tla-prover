---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS Acceptor, Value, Quorum, Ballot

VARIABLES votes, threshold

vars == <<votes, threshold>>

\* A quorum is a set of acceptors; the overlap property (any two quorums share
\* at least one acceptor) is an assumption of the model and not enforced here.
Quorums == {q \in Quorum : Cardinality(q) >= 2}

Voted(v, b) == {a \in Acceptor : <<b, v>> \in votes[a]}
Chosen == {v \in Value : \E q \in Quorums : \A a \in q : \E b \in Ballot : <<b, v>> \in votes[a]}
Never(b) == {a \in Acceptor : \A c \in Ballot : c < b => <<c, v1>> \notin votes[a] /\ <<c, v2>> \notin votes[a]}
Safe(v, b) ==
  \A c \in Ballot : c < b =>
    \E q \in Quorums : \A a \in q : <<c, v>> \in votes[a] \/ a \in Never(c)

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> 0 - 1]

Promised(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* The ballot condition cuts the branching factor: an acceptor stops voting
\* below its own threshold, so it never casts two votes in the same ballot.
VotedIn(b) == {a \in Acceptor : \E v \in Value : <<b, v>> \in votes[a]}

Cast(a, b, v) ==
  /\ b >= threshold[a]
  /\ \A c \in Ballot : <<c, v>> \notin votes[a]
  /\ \A c \in Ballot : c = b => {a2 \in Acceptor : <<c, v2>> \in votes[a2]} = {}
  /\ \E q \in Quorums : \A a2 \in q : Safe(v, b)
  /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next == \E a \in Acceptor, b \in Ballot, v \in Value : Promised(a, b) \/ Cast(a, b, v)

Spec == Init /\ [][Next]_vars

Inv ==
  /\ \A a \in Acceptor, b \in Ballot : \E v \in Value : <<b, v>> \in votes[a] => Safe(v, b)
  /\ \A b \in Ballot : Cardinality(VotedIn(b)) <= 1
  /\ \A a \in Acceptor : threshold[a] \in Ballot \/ threshold[a] = 0 - 1

\* A consensus algorithm implements consensus if the concrete chosen set equals
\* the abstract one derived from the ballots.
ConsensusSpecBar == Chosen = {v \in Value : \E b \in Ballot : \A a \in Acceptor : <<b, v>> \in votes[a]}

MCAcceptor == {a1, a2}
MCValue == {v1, v2}
MCQuorum == {#a1, #a2, {a1, a2}}
MCBallot == 0..2

MCSymmetry == {p \in [Acceptor -> Acceptor] : p[a1] = a2 /\ p[a2] = a1}

====