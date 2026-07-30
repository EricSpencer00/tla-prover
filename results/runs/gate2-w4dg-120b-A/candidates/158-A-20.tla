---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

\* Actors and components: Acceptor, Value, Quorum. The configuration file provides
\* the concrete constants for each; this module declares them so the file-only
\* constants are also visible to the spec.
CONSTANTS Acceptor, Value, Quorum, Ballot

VARIABLES votes, th

vars == <<votes, th>>

Vote == [ac: Acceptor, b: Ballot, v: Value]
QVote == [ac: Acceptor, b: Ballot]

\* Quorums must overlap: this is the additional assumption the spec calls for.
TwoQuorumsIntersect ==
  \A q1 \in Quorum, q2 \in Quorum : \E x \in q1 \cap q2 : TRUE

\* A ballot is safe for a value when every lower ballot is covered by a quorum
\* that either already voted for that value or cannot vote at all.
SafeAt(v, b) ==
  \A c \in 0 .. b - 1 :
    \E q \in Quorum :
      \A x \in q :
        \/ \E e \in votes : e.v = v /\ e.b = c /\ e.ac = x
        \/ th[x] >= c

TypeOK ==
  /\ votes \subseteq Vote
  /\ th \in [Acceptor -> Ballot \cup {-1}]

Init ==
  /\ votes = {}
  /\ th = [x \in Acceptor |-> -1]

Promise(x, b) ==
  /\ b > th[x]
  /\ th' = [th EXCEPT ![x] = b]
  /\ UNCHANGED votes

\* The safety constraint that makes the quorum check worth it: a ballot cannot
\* be voted for two different values.
Vote(x, b, v) ==
  /\ b >= th[x]
  /\ ~(\E e \in votes : e.b = b /\ e.ac = x)
  /\ (\A e \in votes : e.b = b => e.v = v)
  /\ SafeAt(v, b)
  /\ votes' = votes \cup {[ac |-> x, b |-> b, v |-> v]}
  /\ th' = [th EXCEPT ![x] = b]

Next ==
  \/ \E x \in Acceptor, b \in Ballot : Promise(x, b)
  \/ \E x \in Acceptor, b \in Ballot, v \in Value : Vote(x, b, v)

Spec == Init /\ [][Next]_vars

Inv == TypeOK /\ SafeAt \A

\* Chosen values: those a quorum has fully voted for in one ballot. The two
\* quorum-of-votes clauses are the source of the at-most-one guarantee.
Chosen ==
  {v \in Value :
     \E q \in Quorum, b \in Ballot :
       \A x \in q : \E e \in votes : e.v = v /\ e.b = b /\ e.ac = x}

ConsensusSpecBar == Cardinality(Chosen) <= 1

====