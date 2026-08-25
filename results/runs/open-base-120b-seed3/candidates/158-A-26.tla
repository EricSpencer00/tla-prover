---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

MCAcceptor == Acceptor
MCValue   == Value
MCQuorum  == Quorum
MCBallot  == Ballot

VARIABLES votes, thresh

VoteRec == [ballot : Ballot, value : Value]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ thresh = [a \in Acceptor |-> -1]

PromiseIncrease(a, b) ==
  /\ a \in Acceptor
  /\ b \in Ballot
  /\ b > thresh[a]
  /\ votes' = votes
  /\ thresh' = [thresh EXCEPT ![a] = b]

VoteAction(a, b, v) ==
  /\ a \in Acceptor
  /\ b \in Ballot
  /\ v \in Value
  /\ b >= thresh[a]
  /\ \A w \in votes[a] : w.ballot # b
  /\ \A a2 \in Acceptor : \A w \in votes[a2] :
        (w.ballot = b) => w.value = v
  /\ \E Q \in Quorum :
        \A a3 \in Q :
          ( (\E w \in votes[a3] : w.ballot = b /\ w.value = v) \/ thresh[a3] > b )
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b, value |-> v] }]
  /\ thresh' = [thresh EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : PromiseIncrease(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : VoteAction(a, b, v)

Spec == Init /\ [][Next]_<<votes, thresh>>

Safe(b, v) ==
  \A c \in Ballot :
    c < b =>
      \E Q \in Quorum :
        \A a \in Q :
          ( (\E w \in votes[a] : w.ballot = c /\ w.value = v) \/ thresh[a] > c )

AllVoted(Q, b, v) ==
  \A a \in Q : \E w \in votes[a] : w.ballot = b /\ w.value = v

Inv ==
  /\ \A a \in Acceptor : \A w \in votes[a] : Safe(w.ballot, w.value)
  /\ \A b \in Ballot :
        \A v1 \in Value, v2 \in Value :
          ( (\E a1 \in Acceptor : \E w1 \in votes[a1] : w1.ballot = b /\ w1.value = v1) /\
            (\E a2 \in Acceptor : \E w2 \in votes[a2] : w2.ballot = b /\ w2.value = v2) )
          => v1 = v2
  /\ \A a \in Acceptor : thresh[a] >= -1

ConsensusSpecBar ==
  [] ( \A Q1 \in Quorum, Q2 \in Quorum, b1 \in Ballot, b2 \in Ballot, v1 \in Value, v2 \in Value :
        (AllVoted(Q1, b1, v1) /\ AllVoted(Q2, b2, v2)) => v1 = v2 )

IsBijection(f) ==
  /\ \A a1, a2 \in Acceptor : f[a1] = f[a2] => a1 = a2
  /\ \A a \in Acceptor : \E a0 \in Acceptor : f[a0] = a

MCSymmetry == { f \in [Acceptor -> Acceptor] : IsBijection(f) }

====