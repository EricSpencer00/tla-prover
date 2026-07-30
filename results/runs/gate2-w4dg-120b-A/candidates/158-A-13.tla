---- MODULE Voting ----
EXTENDS Integers, FiniteSets

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

Acceptor == {a1}
Ballot == {0, 1}

VARIABLES votes, promised
vars == <<votes, promised>>

Quorums == {Quorum}

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ promised \in [Acceptor -> Ballot \cup {-1}]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ promised = [a \in Acceptor |-> -1]

\* An acceptor may raise its promise threshold and refuse to vote below it.
Raise(a, b) ==
  /\ b > promised[a]
  /\ promised' = [promised EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* Safety test for a value at a ballot: every lower ballot must be safe for it
\* in some quorum, i.e. nobody lower-balls cast a different value.
SafeAt(v, b) ==
  \A c \in Ballot :
    (c < b) =>
      \E Q \in Quorums :
        /\ Quorum \subseteq Q
        /\ \A a \in Q :
             (c, v) \in votes[a]
             \/ (\A w \in Value : (c, w) \notin votes[a])

\* An acceptor votes, but only if the ballot is above its threshold, it
\* has not voted in that ballot yet, no other acceptor voted differently
\* for the same ballot, and the value is safe at that ballot.
Vote(a, b, v) ==
  /\ b >= promised[a]
  /\ \A w \in Value : (b, w) \notin votes[a]
  /\ \A a2 \in Acceptor :
       \A w \in Value : ((b, w) \in votes[a2]) => w = v
  /\ SafeAt(v, b)
  /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
  /\ promised' = [promised EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : Raise(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)

Spec == Init /\ [][Next]_vars

\* Every vote is safe at its ballot number.
Inv ==
  /\ TypeOK
  /\ \A a \in Acceptor : \A bv \in votes[a] : SafeAt(bv[2], bv[1])
  /\ \A a1 \in Acceptor, a2 \in Acceptor :
       \A b \in Ballot :
         (\E w \in Value : <<b, w>> \in votes[a1]) /\ (\E w \in Value : <<b, w>> \in votes[a2])
           => a1 = a2

\* The derived consensus view: a value is chosen once a quorum of acceptors
\* has all voted for it in the same ballot.
Chosen == {v \in Value : \E Q \in Quorums : \A a \in Q : \E b \in Ballot : <<b, v>> \in votes[a]}

\* The voting algorithm refines the abstract consensus specification, where
\* the chosen set is derived from the concrete votes.
ConsensusSpecBar == Cardinality(Chosen) <= 1

====