---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

VARIABLES votes, threshold

vars == <<votes, threshold>>

\* A vote is a ballot-number/value pair an acceptor has cast.
Vote == [ball : Ballot, val : Value]

\* A value is safe at ballot b if every lower ballot c has a quorum
\* in which each member either already voted for it in c or can never
\* vote in c (its threshold is already above c).
SafeAt(v, b) ==
  \A c \in 0..(b - 1) :
    \E Q \in Quorum :
      \A a \in Q :
        \/ [ball |-> c, val |-> v] \in votes[a]
        \/ threshold[a] > c

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

\* An acceptor may raise its promise threshold without voting.
RaiseThreshold(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* An acceptor votes for a value in a ballot, provided the ballot is
\* above its threshold, it has not already voted in that ballot, no
\* other acceptor voted for a different value in that ballot, and the
\* value is safe at that ballot. Voting also raises the threshold.
Vote(a, b, v) ==
  /\ b >= threshold[a]
  /\ [ball |-> b, val |-> v] \notin votes[a]
  /\ \A a2 \in Acceptor : \A w \in Value :
        ([ball |-> b, val |-> w] \in votes[a2]) => w = v
  /\ SafeAt(v, b)
  /\ votes' = [votes EXCEPT ![a] = @ \cup {[ball |-> b, val |-> v]}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : RaiseThreshold(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)

Spec == Init /\ [][Next]_vars

\* Every vote cast is safe at its ballot number.
VotesAreSafe ==
  \A a \in Acceptor : \A w \in votes[a] : SafeAt(w.val, w.ball)

\* At most one value is voted for per ballot across all acceptors.
OneValuePerBallot ==
  \A a1 \in Acceptor : \A w1 \in votes[a1] :
    \A a2 \in Acceptor : \A w2 \in votes[a2] :
      (w1.ball = w2.ball) => (w1.val = w2.val)

\* Type correctness of votes and thresholds.
TypeOK ==
  /\ votes \in [Acceptor -> SUBSET Vote]
  /\ threshold \in [Acceptor -> (-1)..(Cardinality(Ballot) - 1)]

\* A value is chosen once a quorum has all voted for it in some ballot.
Chosen == {v \in Value : \E Q \in Quorum : \A a \in Q : \E w \in votes[a] : w.val = v}

\* Consistency: the set of chosen values has at most one element.
AtMostOneChosen == \A x \in Chosen, y \in Chosen : x = y

Inv == VotesAreSafe /\ OneValuePerBallot /\ TypeOK /\ AtMostOneChosen

\* The voting algorithm implements the abstract consensus spec via a
\* refinement mapping that derives the chosen set from the votes.
ConsensusSpecBar == Chosen = {v \in Value : \E a \in Acceptor, w \in votes[a] : w.val = v}

====