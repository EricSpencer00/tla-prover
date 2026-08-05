---- MODULE Voting ----
EXTENDS Naturals

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

VARIABLES votes, promised
vars == <<votes, promised>>

\* An acceptor votes for a value in a ballot only if every lower ballot has a
\* quorum that is safe for that value, where safety means either already voting
\* for it or no longer able to vote at that ballot.
Safe == {a \in Acceptor : votes[a] = {} \/ \E v \in Value : <<a, v>> \in votes[a]}
NoDouble == {p \in Quorum : \A b \in Ballot : \A v \in Value :
               (b \in promised) => (<<b, v>> \in votes[p] => v = v1)}
TypeOK == /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
          /\ promised \in [Acceptor -> Ballot]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ promised = [a \in Acceptor |-> -1]

Promise(a, b) ==
  /\ b > promised[a]
  /\ promised' = [promised EXCEPT ![a] = b]
  /\ UNCHANGED votes

SafeVote(a, b, v) ==
  /\ b >= promised[a]
  /\ <<b, v>> \notin votes[a]
  /\ \A a2 \in Acceptor : <<b, v>> \in votes[a2] => a2 = a
  /\ \A c \in Ballot : (c < b) =>
       \E Q \in Quorum :
         \A a2 \in Q : (c \in promised => <<c, v>> \in votes[a2]) \/ (c > promised[a2])
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
  /\ promised' = [promised EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : Promise(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : SafeVote(a, b, v)

Spec == Init /\ [][Next]_vars

Inv == /\ TypeOK
       /\ \A a \in Acceptor, b \in Ballot, v \in Value : (<<b, v>> \in votes[a]) => Safe
       /\ NoDouble

\* A quorum voting for a value in a ballot is the concrete choice in the
\* consensus spec; chosen values must all agree (at most one is ever chosen).
ConsensusSpecBar == (CHOOSE v \in Value : \E Q \in Quorum : \A a \in Q : <<0, v>> \in votes[a]) = v1
====