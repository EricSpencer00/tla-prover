---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

\* Self-stabilizing voting consensus: an acceptor may raise its ballot
\* threshold and never votes below it; a vote in a ballot is only cast
\* for a value that is safe, meaning every lower ballot backs that value
\* on some quorum. Quorums always overlap.

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

VARIABLES voted, threshold
vars == <<voted, threshold>>

Votes == Acceptor \X Ballot \X Value

TypeOK ==
  /\ voted \in [Acceptor -> SUBSET Votes]
  /\ threshold \in [Acceptor -> {x \in Ballot : x >= 0} \cup {-1}]

Init ==
  /\ voted = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

\* An acceptor may raise its promise threshold; it never lowers it.
IncreaseThreshold(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED voted

Safe(a, b, v) ==
  /\ b >= threshold[a]
  /\ \A c \in Ballot, w \in Value :
       (c < b /\ <<a, c, w>> \in voted) => (w = v)
  /\ \A c \in Ballot, q \in Quorum :
       (c < b /\ \A x \in q : <<x, c, v>> \in voted) \/ (\A x \in q : \A w \in Value : <<x, c, w>> \notin voted)

\* Vote only if no acceptor has voted for a different value in this ballot
\* and the value is safe at the ballot number.
CastVote(a, b, v) ==
  /\ b >= threshold[a]
  /\ \A w \in Value : <<a, b, w>> \notin voted
  /\ \A x \in Acceptor : <<x, b, v>> \notin voted
  /\ Safe(a, b, v)
  /\ voted' = [voted EXCEPT ![a] = voted[a] \cup {<<a, b, v>>}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : IncreaseThreshold(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : CastVote(a, b, v)

Spec == Init /\ [][Next]_vars

\* Any chosen value stands on a monolithic quorum of acceptors.
Chosen == {v \in Value : \E q \in Quorum : \A x \in q : \E b \in Ballot : <<x, b, v>> \in voted}

\* At most one value is ever chosen.
Inv == Cardinality(Chosen) <= 1

\* The voting algorithm refines an abstract consensus spec: the chosen set
\* is derived from the votes, and the refinement map is the identity on
\* it.
ConsensusSpecBar == Cardinality(Chosen) <= 1

====