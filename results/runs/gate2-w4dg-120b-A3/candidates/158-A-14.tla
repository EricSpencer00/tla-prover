---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

Vote == Ballot \X Value
QuorumVote == {q \in Quorum : (\E x \in Acceptor : x \in q)}
NoValue == "novalue"

VARIABLES votes, threshold

vars == <<votes, threshold>>

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET Vote]
  /\ threshold \in [Acceptor -> Ballot \cup {-1}]

Init ==
  /\ votes = [x \in Acceptor |-> {}]
  /\ threshold = [x \in Acceptor |-> -1]

\* An acceptor raises its promise threshold; it may no longer vote below it.
Raise(x, b) ==
  /\ b > threshold[x]
  /\ threshold' = [threshold EXCEPT ![x] = b]
  /\ UNCHANGED votes

QuorumHas(a, val, b) ==
  /\ a \in Quorum
  /\ \A x \in a : [b |-> val] \in votes[x]

\* Safety check: voting for val in ballot b is safe iff every earlier ballot
\* c < b is covered by a quorum voting for val or by acceptors that cannot vote.
\* The quorum argument here is what makes the non-empty-intersection property
\* useful for reasoning about consistency across ballots.
Safe(x, val, b) ==
  /\ \A c \in 0 .. (b - 1) :
       \E q \in Quorum :
         /\ \A y \in q : [c |-> val] \in votes[y] \/ c < threshold[y]
         /\ \A y \in QuorumHas(q, val, c) : y \in q
  /\ \A y \in Acceptor : [b |-> val] \in votes[y] => y \in QuorumHas(q, val, b)

\* An acceptor may vote only if no other acceptor has voted in this ballot for
\* a different value and only if the value keeps the shared state safe.
Vote(x, val, b) ==
  /\ b >= threshold[x]
  /\ [b |-> val] \notin votes[x]
  /\ \A y \in Acceptor : [b |-> val] \in votes[y] => y = x
  /\ Safe(x, val, b)
  /\ votes' = [votes EXCEPT ![x] = @ \cup {[b |-> val]}]
  /\ threshold' = [threshold EXCEPT ![x] = b]

Next ==
  \/ \E x \in Acceptor, b \in Ballot : Raise(x, b)
  \/ \E x \in Acceptor, val \in Value, b \in Ballot : Vote(x, val, b)

Spec == Init /\ [][Next]_vars

\* Every ballot has at most one voted-for value across all acceptors.
BallotValueUnique ==
  \A x, y \in Acceptor, b \in Ballot, v1, v2 \in Value :
    /\ [b |-> v1] \in votes[x]
    /\ [b |-> v2] \in votes[y]
    => v1 = v2

\* Any quorum voting for a value in a ballot is non-empty.
QuorumNonEmpty ==
  \A x \in Acceptor, b \in Ballot, v \in Value :
    [b |-> v] \in votes[x] => QuorumHas(\E q \in Quorum : q, v, b)

AllVotesSafe ==
  \A x \in Acceptor : \A [b |-> val] \in votes[x] : Safe(x, val, b)

Inv == BallotValueUnique /\ QuorumNonEmpty /\ AllVotesSafe

\* Consistency: if two quorums vote for (possibly different) values in any
\* ballots, those values must be the same -- so at most one value is ever
\* chosen across all ballots.
ConsensusSpecBar ==
  \A a, b \in Quorum :
    \A c, d \in Ballot :
      \A v1, v2 \in Value :
        /\ QuorumHas(a, v1, c)
        /\ QuorumHas(b, v2, d)
        => v1 = v2

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

\* Symmetry: any permutation of the acceptor population leaves the model
\* indistinguishable, which is what lets the model check be kept small.
MCSymmetry == {f \in [Acceptor -> Acceptor] : TRUE}

====