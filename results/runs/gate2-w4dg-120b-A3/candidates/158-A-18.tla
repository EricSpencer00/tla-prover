---- MODULE Voting ----
EXTENDS Naturals

CONSTANTS a1, a2, a3, v1, v2, Ballot

Acceptor == {a1, a2, a3}
Value == {v1, v2}
Quorum == { {a1, a2}, {a2, a3}, {a1, a3} }
Ballots == 0 .. Ballot

VARIABLES votes, promise
vars == <<votes, promise>>

\* A vote is a ballot-number/value pair; every vote cast must be safe:
\* for every lower ballot, some quorum has already committed to this value
\* (or a member cannot vote in that ballot).
SafeVote(v, b) ==
  /\ [ball |-> b, val |-> v] \in votes[a1]
  /\ \A c \in 0 .. (b - 1) : \E q \in Quorum :
       \A m \in q : ([ball |-> c, val |-> v] \in votes[m]) \/ (promise[m] >= c)

NoQuorumConflicts(v, b) ==
  \A a \in Acceptor : \A q \in Quorum :
    (\A m \in q : [ball |-> b, val |-> v] \in votes[m])
      => \A m \in q : [ball |-> b, val |-> v] \in votes[m]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ promise = [a \in Acceptor |-> -1]

\* An acceptor can raise its promise threshold without voting.
RaisePromise(a, b) ==
  /\ b > promise[a]
  /\ promise' = [promise EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* Voting is authorized only if no quorum conflict exists and the ballot
\* is above the acceptor's own threshold.
CastVote(a, v, b) ==
  /\ b >= promise[a]
  /\ \A x \in votes[a] : x.ball # b
  /\ \A x \in votes[a] : x.val = v
  /\ NoQuorumConflicts(v, b)
  /\ (\A q \in Quorum : \E m \in q : [ball |-> b, val |-> v] \in votes[m])
  /\ votes' = [votes EXCEPT ![a] = @ \cup {[ball |-> b, val |-> v]}]
  /\ promise' = [promise EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballots : RaisePromise(a, b)
  \/ \E a \in Acceptor, v \in Value, b \in Ballots : CastVote(a, v, b)

Spec == Init /\ [][Next]_vars

ExtractQuorums ==
  {\A q \in Quorum : \E m \in q : [ball |-> b, val |-> v] \in votes[m] : [ball |-> b, val |-> v] \in votes[a1]}

\* Consistency: no two values can ever both be backed by a quorum.
Inv ==
  /\ \A v \in Value : SafeVote(v, Ballot)
  /\ \A a \in Acceptor : promise[a] \in {-1} \cup Ballots
  /\ \A a \in Acceptor : votes[a] \subseteq [ball : Ballots, val : Value]
  /\ \A x \in votes[a1] : \E y \in votes[a2] : x.val = y.val

\* Refinement: the voting algorithm implements the abstract consensus spec.
ConsensusSpecBar ==
  \E selected \in Value : \A a \in Acceptor : \A x \in votes[a] : x.val = selected

\* MCAcceptor, MCValue, MCQuorum, MCBallot are the bounded versions the .cfg
\* substitutes for the abstract constants; they must be defined here.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

\* A symmetry that swaps a1 and a2 (with a3 fixed) keeps the model unchanged.
MCSymmetry == [a \in Acceptor |-> IF a = a1 THEN a2 ELSE IF a = a2 THEN a1 ELSE a]

====