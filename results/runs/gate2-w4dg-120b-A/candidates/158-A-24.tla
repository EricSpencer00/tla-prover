---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

ASSUME /\ a1 \notin Acceptor
       /\ Quorum \subseteq SUBSET Acceptor
       /\ ~ \E Q1, Q2 \in Quorum : Q1 \cup Q2 = Acceptor

VARIABLES votes, threshold

vars == <<votes, threshold>>

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ threshold \in [Acceptor -> Ballot \cup {-1}]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

\* A vote for v in ballot b is safe only if every lower ballot c is covered
\* by a quorum that either already voted for v in c or can no longer vote.
Safe(a, b, v) ==
  /\ \A c \in 0 .. (b - 1) : \E Q \in Quorum :
        /\ \A x \in Q : (c, v) \in votes[x] \/ threshold[x] > c
        /\ (c, v) \in votes[a]
  /\ \A x \in Acceptor : (b, v) \in votes[x] => threshold[x] <= b

NoDoubleVote(b) ==
  \A a1, a2 \in Acceptor :
    /\ ((b, v) \in votes[a1] /\ (b, w) \in votes[a2]) => v = w

NoDoubleBallot ==
  \A b \in Ballot :
    \A a1, a2 \in Acceptor :
      ((b, v) \in votes[a1] /\ (b, w) \in votes[a2]) => v = w

Next ==
  \/ \E a \in Acceptor, b \in Ballot :
       /\ threshold[a] < b
       /\ threshold' = [threshold EXCEPT ![a] = b]
       /\ UNCHANGED votes
  \/ \E a \in Acceptor, b \in Ballot, v \in Value :
       /\ threshold[a] <= b
       /\ \A x \in Acceptor : (b, v) \notin votes[x]
       /\ \A x \in Acceptor, w \in Value : ((b, w) \in votes[x] /\ w # v) => FALSE
       /\ \E Q \in Quorum : \A x \in Q : \A w \in Value : ((b, w) \in votes[x] /\ w # v) => FALSE
       /\ Safe(a, b, v)
       /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
       /\ threshold' = [threshold EXCEPT ![a] = b]

Spec == Init /\ [][Next]_vars

\* Every chosen value is backed by a full-quorum vote in the same ballot,
\* so the chosen set can never hold two distinct values.
Inv ==
  /\ TypeOK
  /\ \A a \in Acceptor : \A b \in Ballot, v \in Value : ((b, v) \in votes[a]) => Safe(a, b, v)
  /\ NoDoubleVote
  /\ NoDoubleBallot

ConsensusSpecBar == Inv

====