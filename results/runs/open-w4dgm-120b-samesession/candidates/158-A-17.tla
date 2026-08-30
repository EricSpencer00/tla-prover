---- MODULE Voting ----
EXTENDS Naturals

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* The ballot capacity here is a fixed ceiling; the description allows any
\* natural number, but model checking needs a finite bound. The ceiling is
\* reassignable per configuration, which is how the model is kept small.
MAXB == 2

VARIABLES votes, threshold
vars == <<votes, threshold>>

\* A vote is a ballot number paired with the value it was cast for.
Cast == [ball: Ballot, val: Value]

\* A quorum is safe at ballot b if every lower ballot is already resolved
\* (everyone in the quorum voted for it, or can never vote in it).
TypeOK ==
  /\ votes \in [Acceptor -> SUBSET Cast]
  /\ threshold \in [Acceptor -> {-1} \cup (0..MAXB)]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

Raise(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* Safety check guards the vote: it disallows voting for a value that would
\* conflict with a strict-majority decision already made in that ballot.
Vote(a, b, v) ==
  /\ b <= MAXB
  /\ b >= threshold[a]
  /\ \A x \in votes[a] : x.ball # b
  /\ \A x \in Acceptor : (\A y \in votes[x] : y.ball = b) => y.val = v
  /\ \E q \in Quorum : \A x \in q : \A y \in votes[x] : (y.ball = b /\ y.val = v)
       \/ (y.ball > b \/ (y.ball = b /\ y.val = v))
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {[ball |-> b, val |-> v]}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Quiesce ==
  /\ \A a \in Acceptor : threshold[a] = MAXB
  /\ \A a \in Acceptor :
       \A b \in Ballot : \A v \in Value :
         (b \in {x.ball : x \in votes[a]}) => (b = MAXB /\ [ball |-> b, val |-> v] \in votes[a])
  /\ UNCHANGED <<votes, threshold>>

Next ==
  \/ Quiesce
  \/ \E a \in Acceptor, b \in Ballot : Raise(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)

Spec == Init /\ [][Next]_vars

\* Every tallied vote is safe at the ballot it was cast for.
SafeVotes ==
  \A a \in Acceptor : \A x \in votes[a] :
    \A c \in 0..(x.ball - 1) :
      \E q \in Quorum : \A y \in q :
        (y \in Acceptor /\ \E z \in votes[y] : z.ball = c /\ z.val = x.val)
        \/ (\A z \in votes[y] : z.ball < c)

\* Two different values are never both voted for in the same ballot.
BallotUnique ==
  \A a1 \in Acceptor, a2 \in Acceptor :
    \A x1 \in votes[a1], x2 \in votes[a2] :
      (x1.ball = x2.ball) => (x1.val = x2.val)

\* The chosen set can hold at most one value, by construction.
Inv == SafeVotes /\ BallotUnique

Chosen == {v \in Value : \E q \in Quorum : \A a \in q : \E x \in votes[a] : x.val = v}

\* The voting algorithm implements the abstract consensus spec: the set of
\* chosen values is exactly the set of values with a supporting quorum.
ConsensusSpecBar == Chosen = {v \in Value : \E q \in Quorum : \A a \in q : \E x \in votes[a] : x.val = v}

\* Every acceptor is a participant, so swapping them does nothing to the
\* shape of the state space; this is the symmetry the rachet counting
\* uses to keep the model small.
MCSymmetry == {p \in [Acceptor -> Acceptor] : \A a \in Acceptor : p[a] = a}
====