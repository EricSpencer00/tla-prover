---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

VARIABLES Votes, Threshold

Vote == << _ , _ >>
VotesSet == [a \in Acceptor |-> SUBSET Vote]

(* Initial state *)
Init ==
  /\ Votes = [a \in Acceptor |-> {}]
  /\ Threshold = [a \in Acceptor |-> -1]

(* Helper predicate: value v is safe at ballot b *)
IsSafe(v, b) ==
  \A c \in Ballot :
    c < b =>
      \E Q \in Quorum :
        \A a \in Q :
          ( <<c, v>> \in Votes[a] \/ Threshold[a] > c)

(* Actions *)
Promise(a) ==
  \E newTh \in Ballot :
    /\ newTh > Threshold[a]
    /\ Threshold' = [Threshold EXCEPT ![a] = newTh]
    /\ Votes' = Votes

VoteAct(a, b, v) ==
  /\ b \in Ballot
  /\ v \in Value
  /\ b >= Threshold[a]
  /\ <<b, v>> \notin Votes[a]
  /\ \A a' \in Acceptor : a' \neq a /\ <<b, v2>> \in Votes[a'] => v2 = v
  /\ IsSafe(v, b)
  /\ Threshold' = [Threshold EXCEPT ![a] = b]
  /\ Votes'   = [Votes EXCEPT ![a] = Votes[a] \cup { <<b, v>> }]

Next ==
  \E a \in Acceptor :
    ( Promise(a) \/ \E b \in Ballot, v \in Value : VoteAct(a, b, v) )

Spec ==
  Init /\ [][Next]_<<Votes, Threshold>>

(* Invariant components *)
SafeVotes ==
  \A a \in Acceptor :
    \A vote \in Votes[a] :
      IsSafe(vote[2], vote[1])

QuorumSafety ==
  \A b1, b2 \in Ballot :
    \A v1, v2 \in Value :
      \A Q1, Q2 \in Quorum :
        (\A a \in Q1 : <<b1, v1>> \in Votes[a] ) /\
        (\A a \in Q2 : <<b2, v2>> \in Votes[a] ) => v1 = v2

ThresholdType ==
  \A a \in Acceptor : Threshold[a] \in Ballot \/ Threshold[a] = -1

Inv == SafeVotes /\ QuorumSafety /\ ThresholdType

ConsensusSpecBar == Inv

====