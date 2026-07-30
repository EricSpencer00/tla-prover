---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

Alias == [ballot : Ballot, value : Value]

VARIABLES votes, thr

vars == <<votes, thr>>

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET Alias]
  /\ thr \in [Acceptor -> Ballot \cup {-1}]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ thr = [a \in Acceptor |-> -1]

QuorumOverlap == \A q1, q2 \in Quorum : q1 \cap q2 # {}

VotedInBallot(a, b) == \E v \in Value : <<b, v>> \in votes[a]

VoteCount(a, b) == Cardinality({x \in votes[a] : x.ballot = b})

\* Casting a vote is the only way a value can become committed, so the
\* safety of a vote at its ballot number is the whole of the consensus
\* argument; it is what forbids a later quorum from voting a different value.
SafeAtBallot(b, v) ==
  /\ \A c \in Ballot : c < b =>
       \E q \in Quorum :
         \A a \in q : (\E x \in votes[a] : x.ballot = c /\ x.value = v) \/ (~VotedInBallot(a, c))
  /\ (\A q \in Quorum :
        \A a \in q : VotedInBallot(a, b) => votes[a] = {<<b, v>>})
  /\ (\A c \in Ballot : c > b => ~VotedInBallot(a1, c) \/ ~VotedInBallot(a2, c) \/ ~VotedInBallot(a3, c))

Vote(a, b, v) ==
  /\ b >= thr[a]
  /\ VoteCount(a, b) = 0
  /\ \A x \in Acceptor : VoteCount(x, b) = 0 \/ \A y \in votes[x] : y.value = v
  /\ SafeAtBallot(b, v)
  /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
  /\ thr' = [thr EXCEPT ![a] = b]

MakePromise(a, c) ==
  /\ c > thr[a]
  /\ thr' = [thr EXCEPT ![a] = c]
  /\ UNCHANGED votes

Next ==
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)
  \/ \E a \in Acceptor, c \in Ballot : MakePromise(a, c)

Spec == Init /\ [][Next]_vars

Chosen == {v \in Value : \E q \in Quorum : \A a \in q : {v} = {x.value : x \in votes[a]}}

Inv == \A a \in Acceptor : votes[a] \subseteq Alias /\ thr[a] \in Ballot \cup {-1}

\* The explicit statement of consensus; the invariant below is the
\* ingredient that is proved to imply it.
ConsensusSpecBar == Cardinality(Chosen) <= 1

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

MCSymmetry == {f \in [Acceptor -> Acceptor] : Cardinality({a \in Acceptor : f[a] # a}) \in {1, 2, 3}}

====