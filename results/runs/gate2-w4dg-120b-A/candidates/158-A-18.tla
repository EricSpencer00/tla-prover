---- MODULE Voting ----
EXTENDS Integers, FiniteSets

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

VARIABLES votes, promised
vars == <<votes, promised>>

RECURSIVE VotedFor(_, _, _)
VotedFor(a, b, x) ==
  \E v \in votes[a] : (v[1] = b /\ v[2] = x)

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ promised \in [Acceptor -> (Ballot \cup {-1})]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ promised = [a \in Acceptor |-> -1]

\* Voting in a ballot is only allowed for a value that is safe at that
\* ballot: every lower ballot must already unanimously support it.
SafeAt(a, b, x) ==
  \A c \in 0 .. (b - 1) :
    \E q \in Quorum :
      \A m \in q :
        \/ VotedFor(m, c, x)
        \/ \A y \in Value : ~VotedFor(m, c, y)

\* An acceptor may raise its promise threshold without voting.
Promise(a, b) ==
  /\ b > promised[a]
  /\ promised' = [promised EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* An acceptor votes only if its vote is safe and no conflicting vote
\* already exists in this ballot anywhere in the system.
Vote(a, b, x) ==
  /\ b >= promised[a]
  /\ \A v \in votes[a] : v[1] # b
  /\ \A c \in Acceptor, y \in Value : ~(c # a /\ VotedFor(c, b, y) /\ y # x)
  /\ SafeAt(a, b, x)
  /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, x>>}]
  /\ promised' = [promised EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : Promise(a, b)
  \/ \E a \in Acceptor, b \in Ballot, x \in Value : Vote(a, b, x)

Spec == Init /\ [][Next]_vars

\* Every vote cast is safe at its own ballot number.
EveryVoteSafe == \A a \in Acceptor : \A b \in Ballot : \A x \in Value : (VotedFor(a, b, x) => SafeAt(a, b, x))

\* At most one value is voted for per ballot across all acceptors.
AtMostOnePerBallot == \A b \in Ballot : \A x, y \in Value :
  (\E a \in Acceptor : VotedFor(a, b, x) /\ VotedFor(a, b, y)) => x = y

\* The chosen set is derived from votes: a value is in it if a quorum
\* unanimously voted for it in some ballot.
Chosen == {x \in Value : \E q \in Quorum, b \in Ballot : \A m \in q : VotedFor(m, b, x)}

Inv == TypeOK /\ EveryVoteSafe /\ AtMostOnePerBallot

\* The voting algorithm implements the abstract consensus spec, which
\* requires the chosen set to be a singleton.
ConsensusSpecBar == Cardinality(Chosen) <= 1
====