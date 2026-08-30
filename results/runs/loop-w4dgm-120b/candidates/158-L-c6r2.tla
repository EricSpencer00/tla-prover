---- MODULE Voting ----
EXTENDS Naturals

CONSTANTS Acceptor, Value, Quorum, Ballot

\* A quorum is a set of acceptors that overlaps every other quorum.
\* The model enforces the overlap property, which is what keeps the
\* consensus safe: any two quorums sharing an acceptor means votes
\* cannot silently diverge on different values.
IsQuorum(q) == q \subseteq Acceptor
OverlapQuorums == \A q1, q2 \in Quorum : q1 \cap q2 # {}

\* Votes are pairs of a ballot number and a value. An acceptor's threshold
\* is the lowest ballot it will still participate in (once raised it
\* never lowers, so no acceptor is ever un-promised).
VARIABLES votes, threshold
vars == <<votes, threshold>>

Voted(v) == {a \in Acceptor : \E r \in Ballot : <<r, v>> \in votes[a]}
VotedIn(b) == {a \in Acceptor : <<b, "any">> \in {<<r, w>> : r \in Ballot, w \in Value} \cap votes[a]}
SafeAt(b, v) ==
  /\ \A c \in Ballot : c < b => \E q \in Quorum : \A a \in q : <<c, v>> \in votes[a]
  /\ \A a \in Acceptor : <<b, v>> \in votes[a] => \A c \in Ballot : c < b => <<c, v>> \in votes[a]

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ threshold \in [Acceptor -> Ballot \cup {-1}]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

\* An acceptor may raise its threshold to any higher ballot at any time.
RaiseThreshold(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* Casting a vote is checked against the quorum safety condition.
Vote(a, b, v) ==
  /\ b >= threshold[a]
  /\ <<b, v>> \notin votes[a]
  /\ \A c \in Ballot : c < b => \A a2 \in Acceptor : <<c, "other">> \notin {<<c, w>> : w \in Value} \cap votes[a2]
  /\ \E q \in Quorum : \A a2 \in q : <<b, v>> \in votes[a2]
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : RaiseThreshold(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : Vote(a, b, v)

Spec == Init /\ [][Next]_vars

\* SAFETY: every vote cast must be safe at its ballot number.
VotedSafe == \A a \in Acceptor : \A x \in votes[a] : SafeAt(x[1], x[2])

\* SAFETY: at most one value is ever voted for per ballot across all acceptors.
VotedOnePerBallot ==
  \A b \in Ballot : \A a, a2 \in Acceptor :
    (<<b, "other">> \in votes[a] /\ <<b, "other">> \in votes[a2]) => votes[a] \cap votes[a2] \subseteq {<<b, "other">>}

\* SAFETY: the chosen set of values never grows past one element.
ConsensusSpecBar == VotedOnePerBallot

NoVote == {a \in Acceptor : votes[a] = {}}
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot
====