---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS Acceptor, Value, Quorum, Ballot

VARIABLES votes, thresh
vars == <<votes, thresh>>

VotedFor(v) == {a \in Acceptor : \E b \in Ballot : <<b, v>> \in votes[a]}
VotedIn(b) == {a \in Acceptor : <<b, v>> \in votes[a] : v \in Value}
QuorumHasVotedFor(q, b, v) == \A a \in q : <<b, v>> \in votes[a]
VotersInBallots == UNION {VotedIn(b) : b \in Ballot}
Chosen == {v \in Value : \E q \in Quorum : \A a \in q : <<b, v>> \in votes[a] : b \in Ballot}

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ thresh \in [Acceptor -> Ballot \cup {-1}]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ thresh = [a \in Acceptor |-> -1]

VoteSafe(a, b, v) ==
  /\ b >= thresh[a]
  /\ ~\E c \in Ballot : <<c, v>> \in votes[a]
  /\ ~\E c \in Ballot, w \in Value :
       c < b /\ <<c, w>> \in votes[a] /\ w # v
  /\ \E q \in Quorum :
       /\ \A d \in 0 .. (b - 1) : QuorumHasVotedFor(q, d, v)
       /\ \A c \in 0 .. b : \A w \in Value :
            (~QuorumHasVotedFor(q, c, w) /\ w # v) => c \notin thresh
  /\ VotedIn(b) \subseteq VotersInBallots

MakePromise(a, b) ==
  /\ b > thresh[a]
  /\ thresh' = [thresh EXCEPT ![a] = b]
  /\ UNCHANGED votes

CastVote(a, b, v) ==
  /\ VoteSafe(a, b, v)
  /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
  /\ thresh' = [thresh EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : MakePromise(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : CastVote(a, b, v)

Spec == Init /\ [][Next]_vars

Inv ==
  /\ \A a \in Acceptor, b \in Ballot, v \in Value : <<b, v>> \in votes[a] => VoteSafe(a, b, v)
  /\ \A b \in Ballot, v, w \in Value :
       ((VotedFor(v) \cap VotedIn(b) # {}) /\ (VotedFor(w) \cap VotedIn(b) # {})) => v = w
  /\ TypeOK

ConsensusSpecBar ==
  \A q \in Quorum : Cardinality(VotedIn(b) \cap q) <= 1

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot
MCSymmetry == {id}

====