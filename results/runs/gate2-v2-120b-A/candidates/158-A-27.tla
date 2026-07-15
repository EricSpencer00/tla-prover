---- MODULE Voting ----
EXTENDS Naturals, Sequences, FiniteSets

\* ----------------------------------------------------------------------
\* Constants (instantiated in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANT a1
CONSTANT Acceptor
CONSTANT Value
CONSTANT Quorum
CONSTANT Ballot

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Acceptors == Acceptor
Values    == Value
Quorums   == Quorum
Ballots   == Ballot

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Vote == [b : Ballots, v : Values]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES votes, prom

\* votes   : [Acceptor -> SUBSET Vote]   -- votes cast by each acceptor
\* prom    : [Acceptor -> Nat]           -- promise threshold (minimum ballot)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
SafeAt(v, b) ==
  \A c \in Ballots :
    (c < b) =>
      \E q \in Quorums :
        \A a \in q :
          ( \E w \in Values : [b |-> c, v |-> w] \in votes[a] ) \/
          (\A w \in Values : [b |-> c, v |-> w] \notin votes[a])

QuorumVoted(q, b, v) ==
  \A a \in q : [b |-> b, v |-> v] \in votes[a]

ChosenValues ==
  { v \in Values : \E b \in Ballots : \E q \in Quorums : QuorumVoted(q, b, v) }

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ votes = [a \in Acceptors |-> {}]
  /\ prom  = [a \in Acceptors |-> -1]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
IncreasePromise(a, b) ==
  /\ a \in Acceptors
  /\ b \in Ballots
  /\ b > prom[a]
  /\ prom' = [prom EXCEPT ![a] = b]
  /\ UNCHANGED votes

Vote(a, b, v) ==
  /\ a \in Acceptors
  /\ b \in Ballots
  /\ v \in Values
  /\ b >= prom[a]
  /\ \A a2 \in Acceptors : ~([b |-> b, v |-> v] \in votes[a2])
  /\ \A a2 \in Acceptors, b2 \in Ballots :
        ([b2 |-> b2, v |-> v] \in votes[a2]) => b2 = b
  /\ \E q \in Quorums : \A a2 \in q : SafeAt(v, b)
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [b |-> b, v |-> v] }]
  /\ prom'  = [prom  EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptors, b \in Ballots : IncreasePromise(a, b)
  \/ \E a \in Acceptors, b \in Ballots, v \in Values : Vote(a, b, v)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<votes, prom>>

\* ----------------------------------------------------------------------
\* Invariant required by the .cfg
\* ----------------------------------------------------------------------
Inv == /\ \A a \in Acceptors : prom[a] >= -1
       /\ \A a \in Acceptors : votes[a] \subseteq { [b |-> b, v |-> v] : b \in Ballots, v \in Values }

\* ----------------------------------------------------------------------
\* Property that the algorithm implements consensus
\* (the set of chosen values never contains more than one element)
\* ----------------------------------------------------------------------
ConsensusSpecBar == 
  \A b1 \in Ballots, q1 \in Quorums, v1 \in Values,
      b2 \in Ballots, q2 \in Quorums, v2 \in Values :
        (QuorumVoted(q1, b1, v1) /\ QuorumVoted(q2, b2, v2)) => v1 = v2

====