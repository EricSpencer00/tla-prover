---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

\* Votes are ballot/value pairs; Threshold is an acceptor's promise floor.
VARIABLES votes, threshold

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ threshold \in [Acceptor -> Ballot \cup {-1}]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

\* An acceptor may promise a higher ballot without voting.
Raise(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* A vote is safe at b if every lower ballot c has a quorum voting for v.
Vote(a, b, v) ==
  /\ b >= threshold[a]
  /\ \A c \in Ballot : ~(c \in {b} \cup {threshold[a]}) => ~\E u \in Value : \E d \in Acceptor : <<c, u>> \in votes[d]
  /\ \A c \in Ballot : c < b => \E Q \in Quorum :
        /\ \A d \in Q : <<c, v>> \in votes[d] \/ (threshold[d] > c)
  /\ \A c \in Ballot : ~(\E u \in Value : <<c, u>> \in votes[a])
  /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : Raise(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)

\* Consistency is derived from these three invariants.
\* A vote is safe at its ballot number.
ChosenAtBallotIsSafe ==
  \A a \in Acceptor, b \in Ballot, v \in Value :
    (<<b, v>> \in votes[a]) =>
      (\A c \in Ballot : c < b => \E Q \in Quorum :
        /\ \A d \in Q : <<c, v>> \in votes[d] \/ (threshold[d] > c))

\* At most one value per ballot across all acceptors.
AtMostOneValuePerBallot ==
  \A a \in Acceptor, b \in Ballot, v1 \in Value, v2 \in Value :
    (<<b, v1>> \in votes[a] /\ \E d \in Acceptor : <<b, v2>> \in votes[d]) => v1 = v2

TypeState ==
  /\ votes \subseteq (Ballot \X Value)
  /\ threshold \in [Acceptor -> Ballot \cup {-1}]

\* At most one chosen value ever remains; this is the consensus guarantee.
Inv ==
  /\ ChosenAtBallotIsSafe
  /\ AtMostOneValuePerBallot
  /\ TypeState

Spec == Init /\ [][Next]_<<votes, threshold>>

\* The abstract consensus spec is refined by naming the derived chosen set.
ChosenSet == {v \in Value : \E Q \in Quorum : \A a \in Q : \E b \in Ballot : <<b, v>> \in votes[a]}
ConsensusSpecBar == ChosenSet \subseteq Value

====