---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS Acceptor, Value, Quorum, Ballot

Vote == [ac : Acceptor, b : Ballot, v : Value]
Majority(v) == {q \in Quorum : \A a \in q : [ac |-> a, b |-> 0, v |-> v] \in votes}

VARIABLES votes, promised

vars == <<votes, promised>>

Init ==
  /\ votes = {}
  /\ promised = [a \in Acceptor |-> -1]

Safe(b, v) ==
  \A c \in 0 .. b - 1 : \E q \in Quorum : \A a \in q :
    (([ac |-> a, b |-> c, v |-> v] \in votes) \/ (promised[a] > c))

Cast(a, b, v) ==
  /\ b >= promised[a]
  /\ \A x \in votes : x.b = b => x.v = v
  /\ \E q \in Quorum : \A a2 \in q : (a2 = a \/ [ac |-> a2, b |-> b, v |-> v] \in votes)
  /\ Safe(b, v)
  /\ votes' = votes \cup {[ac |-> a, b |-> b, v |-> v]}
  /\ promised' = [promised EXCEPT ![a] = b]

Promise(a, b) ==
  /\ b > promised[a]
  /\ promised' = [promised EXCEPT ![a] = b]
  /\ UNCHANGED votes

Next ==
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : Cast(a, b, v)
  \/ \E a \in Acceptor, b \in Ballot : Promise(a, b)

QuorumsOverlap ==
  \A p, q \in Quorum : p # q => (p \cap q) # {}

TypeOK ==
  /\ votes \subseteq [ac : Acceptor, b : Ballot, v : Value]
  /\ promised \in [Acceptor -> (-1) \cup Ballot]
  /\ QuorumsOverlap

VoterSafety ==
  \A x \in votes : Safe(x.b, x.v)

BallotChoiceUnique ==
  \A x, y \in votes : x.b = y.b => x.v = y.v

Inv == TypeOK /\ VoterSafety /\ BallotChoiceUnique

Spec == Init /\ [][Next]_vars

SAFETY ==
  \A v \in Value : (Majority(v) => \A w \in Value : Majority(w) => w = v)

CONSISTENCY == \A q \in Quorum : \A x \in q : \A y \in q : x.v = y.v

MCAcceptor == {"a1", "a2"}
MCValue == {"v1", "v2"}
MCQuorum == {{"a1", "a2"}, {"a2", "a3"}, {"a1", "a3"}}
MCBallot == {0, 1}

MCSymmetry == {("a1", "a2"), ("a2", "a1"), ("a2", "a3"), ("a3", "a2")}
====