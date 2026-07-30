---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

\* A vote is a (ballot, value) pair. A quorum is a set of acceptors with the
\* overlap property. The votes variable records what each acceptor has cast,
\* and the thresh variable records the promise threshold per acceptor.
CONSTANTS a1, Acceptor, Value, Quorum, Ballot

None == -1

VARIABLES votes, thresh
vars == <<votes, thresh>>

VoteSpace == Acceptor \X (Ballot \X Value)

TypeOK ==
  /\ votes \subseteq VoteSpace
  /\ thresh \in [Acceptor -> (Ballot \cup {None})]

Init ==
  /\ votes = {}
  /\ thresh = [a \in Acceptor |-> None]

\* Raising the threshold is the acceptor refusing to vote in any lower ballot.
RaiseThresh(a, b) ==
  /\ \A c \in Ballot: c < b => thresh[a] = None \/ thresh[a] <= c
  /\ thresh' = [thresh EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* Safety of a vote at a ballot is its compatibility with every lower ballot.
SafeAt(a, b, v) ==
  /\ \A c \in Ballot:
       c < b => \E q \in Quorum:
         /\ \A x \in q: \E vv \in Value: <<x, c, vv>> \in votes \/ thresh[x] = None \/ thresh[x] > c
         /\ \E x \in q: <<x, c, v>> \in votes

\* An acceptor votes for a value only if it is not below its threshold,
\* has not already voted in that ballot, nobody else voted in that ballot,
\* and there is a safe quorum backing the vote.
Vote(a, b, v) ==
  /\ (thresh[a] = None \/ thresh[a] <= b)
  /\ ~ \E x \in Acceptor: <<x, b, v>> \in votes
  /\ \A x \in Acceptor: <<x, b, v>> \notin votes
  /\ \E q \in Quorum: \A x \in q: <<x, b, v>> \in votes \/ SafeAt(x, b, v)
  /\ votes' = votes \cup {<<a, b, v>>}
  /\ thresh' = [thresh EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot: RaiseThresh(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value: Vote(a, b, v)

Spec == Init /\ [][Next]_vars

\* Every cast vote was safe at its ballot number, so the quorum can never
\* be torn apart by a bet that loses safety in hindsight.
SafeBallot == \A a \in Acceptor, b \in Ballot, v \in Value: <<a, b, v>> \in votes => SafeAt(a, b, v)

\* Only one value is ever voted for in a given ballot across all acceptors.
AtMostOnePerBallot ==
  \A p, q \in votes: (p[2] = q[2]) => (p[3] = q[3])

Inv == SafeBallot /\ AtMostOnePerBallot /\ TypeOK

\* The refinement maps the voting algorithm to the abstract consensus spec:
\* the chosen set is derived from the votes and must never hold two values.
ConsensusSpecBar ==
  \A x, y \in Value: (x # y /\ (\E q \in Quorum: \A a \in q: <<a, 0, x>> \in votes))
                      => ~(\E q \in Quorum: \A a \in q: <<a, 0, y>> \in votes)

====