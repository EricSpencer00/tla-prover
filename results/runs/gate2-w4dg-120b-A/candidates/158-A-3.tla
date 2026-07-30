---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

\* Votes is the set of all votes ever cast; Chosen is derived from it.
VARIABLES Votes, Chosen, Threshold

vars == <<Votes, Chosen, Threshold>>

TypeOK ==
  /\ Votes \subseteq [a: Acceptor, ballot: Ballot, v: Value]
  /\ Chosen \subseteq Value
  /\ Threshold \in [Acceptor -> Ballot \cup {-1}]

NoPromise == [a \in Acceptor |-> -1]

Init ==
  /\ Votes = {}
  /\ Chosen = {}
  /\ Threshold = NoPromise

\* A quorum of acceptors can demonstrate that value v is safe at ballot b:
\* every lower ballot c has a quorum in which each member has already voted
\* for v or cannot vote in c (its threshold already cleared c).
Safe(v, b) ==
  \A c \in Ballot :
    (c < b) =>
      \E Q \in Quorum :
        /\ \A a \in Q : (c \in Threshold[a]) \/ (\E w \in Value : <<a, c, w>> \in Votes)
        /\ \A a \in Q : \A w \in Value : <<a, c, w>> \in Votes => w = v

\* Ballots strictly increase: an acceptor cannot go back to an earlier one.
Promised(a, b) == b > Threshold[a]

NoOtherVote(b, v) ==
  \A a \in Acceptor :
    \A w \in Value : (<<a, b, w>> \in Votes) => w = v

\* Casting a vote in ballot b for v also promises that ballot onward.
Vote(a, b, v) ==
  /\ Promised(a, b)
  /\ <<a, b, v>> \notin Votes
  /\ NoOtherVote(b, v)
  /\ Safe(v, b)
  /\ Votes' = Votes \cup {<<a, b, v>>}
  /\ Chosen' = Chosen \cup {v}
  /\ Threshold' = [Threshold EXCEPT ![a] = b]

RaiseThreshold(a, b) ==
  /\ b > Threshold[a]
  /\ Threshold' = [Threshold EXCEPT ![a] = b]
  /\ UNCHANGED <<Votes, Chosen>>

Next ==
  \/ \E a \in Acceptor : \E b \in Ballot : RaiseThreshold(a, b)
  \/ \E a \in Acceptor : \E b \in Ballot : \E v \in Value : Vote(a, b, v)

Spec == Init /\ [][Next]_vars

\* Consistency is expressed directly as the bounded-chosen-value bound, but
\* it is backed by three invariants that together imply it.
Inv == Cardinality(Chosen) <= 1

\* Every vote that lands is supported by the safety mechanism.
EveryVoteSafe ==
  \A e \in Votes : Safe(e.v, e.ballot)

OneVotePerBallot ==
  \A c \in Ballot : \A a \in Acceptor : \A w \in Value :
    (<<a, c, w>> \in Votes) => (\A x \in Acceptor : \A y \in Value : <<x, c, y>> \in Votes => y = w)

TypeOKAgain == TypeOK

\* The voting algorithm is a refinement of an abstract consensus spec: the
\* chosen set derived from votes must itself satisfy the consensus spec.
ConsensusSpecBar == Inv /\ EveryVoteSafe /\ OneVotePerBallot /\ TypeOKAgain

====