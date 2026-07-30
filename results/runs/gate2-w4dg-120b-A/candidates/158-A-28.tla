---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

VARIABLES votes, threshold

vars == <<votes, threshold>>

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ threshold \in [Acceptor -> (Ballot \cup {-1})]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

Promise(a, b) ==
  /\ threshold[a] < b
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

Vote(a, b, v) ==
  /\ threshold[a] <= b
  /\ \A w \in votes[a] : w[1] # b
  /\ ~(\E c \in Acceptor, w \in votes[c] : w[1] = b /\ w[2] # v)
  /\ \E q \in Quorum :
       /\ \A c \in q : b >= threshold[c]
       /\ \A c \in q : (\A d \in (0 .. (b - 1)) : \E w \in votes[c] : w[1] = d /\ w[2] = v)
  /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : Promise(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)

Spec == Init /\ [][Next]_vars

VotedSet == {v \in Value : \E a \in Acceptor, b \in Ballot : <<b, v>> \in votes[a]}

ChosenVal(v) == \E a \in Acceptor, b \in Ballot : <<b, v>> \in votes[a]

Inv ==
  /\ \A a \in Acceptor, w \in votes[a] : w[2] \in Value
  /\ \A a, c \in Acceptor : \A b \in Ballot :
       /\ <<b, v>> \in votes[a] => \A w \in votes[c] : w[1] = b => w[2] = v
  /\ TypeOK

ConsensusSpecBar == \A v \in Value : ChosenVal(v) => v \in VotedSet

====