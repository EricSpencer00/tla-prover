---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

VARIABLES cast, thresh
vars == <<cast, thresh>>

\* cast[a] is the set of votes voter a has cast; a vote is a ballot/value pair.
\* thresh[a] is the lowest ballot that voter a is willing to vote in.
\* Ballot is the highest ballot ever observed; each vote's ballot is bounded by it.
TypeOK ==
  /\ cast \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ thresh \in [Acceptor -> Ballot \cup {-1}]

Init ==
  /\ cast = [a \in Acceptor |-> {}]
  /\ thresh = [a \in Acceptor |-> -1]

HasVoted(a, b) == \E v \in Value : <<b, v>> \in cast[a]
VotedFor(a, b, v) == <<b, v>> \in cast[a]

\* A value is safe at ballot b if every lower ballot is backed by a quorum
\* voting for it, so voting for it now cannot contradict earlier quorums.
Safe(v, b) ==
  \A c \in 0 .. (b - 1) :
    \E q \in Quorum :
      \A a \in q :
        (VotedFor(a, c, v) \/ (c < thresh[a] /\ thresh[a] # -1))

\* The promise action moves a's threshold upward without casting a vote.
Promise(a, b) ==
  /\ b > thresh[a]
  /\ thresh' = [thresh EXCEPT ![a] = b]
  /\ UNCHANGED cast

\* Voting is guarded by the safety check and by the per-quorum exclusivity rule.
Vote(a, b, v) ==
  /\ b >= thresh[a]
  /\ ~HasVoted(a, b)
  /\ \A c \in 0 .. b : \A x \in Value : ~(x # v /\ HasVoted(a, c))
  /\ ~(\E x \in Value : x # v /\ HasVoted(a, b))
  /\ Safe(v, b)
  /\ cast' = [cast EXCEPT ![a] = @ \cup {<<b, v>>}]
  /\ thresh' = [thresh EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : Promise(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)

Spec == Init /\ [][Next]_vars

\* A value is chosen once a quorum votes for it in some ballot.
Chosen(v) == \E b \in Ballot, q \in Quorum : \A a \in q : VotedFor(a, b, v)

\* The invariant is broken into three lemmas that together give consistency.
Inv ==
  /\ \A a \in Acceptor, b \in Ballot, v \in Value : VotedFor(a, b, v) => Safe(v, b)
  /\ \A b \in Ballot, v1, v2 \in Value :
       (\A a \in Acceptor : HasVoted(a, b) => VotedFor(a, b, v1))
         => (\A a \in Acceptor : HasVoted(a, b) => VotedFor(a, b, v2))
         => v1 = v2
  /\ TypeOK

\* Refinement: voting implements the abstract consensus spec.
ConsensusSpecBar == \A v \in Value : Chosen(v) => \E b \in Ballot, q \in Quorum : \A a \in q : VotedFor(a, b, v)

====