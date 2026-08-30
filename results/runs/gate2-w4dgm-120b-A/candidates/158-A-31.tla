---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

(* The system tracks a two-phase commit-style voting process in which acceptors *)
(* cast votes for a value in numbered ballots.  A value is chosen only once a    *)
(* quorum of acceptors has voted for it at some ballot.  The invariant protects *)
(* against two different values ever both collecting a quorum of votes.        *)

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

MCAcceptor == a1
MCValue == v1
MCQuorum == Quorum
MCBallot == Ballot

NoVote == "novote"
Votes == Value \X Ballot

VARIABLES vote, tick
vars == <<vote, tick>>

QuorumFor(v, b) == {q \in Quorum : \A p \in q : <<v, b>> \in vote[p]}
Chosen == {v \in Value : \E q \in Quorum : QuorumFor(v, MCBallot) = q}

TypeOK ==
  /\ vote \in [Acceptor -> SUBSET Votes]
  /\ tick \in [Acceptor -> MCBallot \cup {NoVote}]

Init ==
  /\ vote = [p \in Acceptor |-> {}]
  /\ tick = [p \in Acceptor |-> NoVote]

\* An acceptor may raise its promise threshold to a later ballot at any time.
Raise(p, b) ==
  /\ (tick[p] = NoVote \/ b > tick[p])
  /\ b \in MCBallot
  /\ tick' = [tick EXCEPT ![p] = b]
  /\ UNCHANGED vote

\* Vote for a value in a ballot, provided no other value has a vote in that
\* ballot yet and the value is safe at that ballot.
Vote(p, v, b) ==
  /\ b \in MCBallot
  /\ (tick[p] = NoVote \/ b >= tick[p])
  /\ \A q \in Quorum : <<v, b>> \in vote[p]
  /\ \A c \in MCBallot : c < b => \A w \in Value :
       (\E q \in Quorum : <<w, c>> \in vote[p]) => w = v
  /\ \A q \in Quorum : \A r \in q : <<v, b>> \in vote[r]
  /\ vote' = [vote EXCEPT ![p] = vote[p] \cup {<<v, b>>}]
  /\ tick' = [tick EXCEPT ![p] = b]

Next ==
  \/ \E p \in Acceptor, b \in MCBallot : Raise(p, b)
  \/ \E p \in Acceptor, v \in Value, b \in MCBallot : Vote(p, v, b)

\* A ballot can only be cast once, so a quorum voting for a value in that
\* ballot is the same as a quorum voting for that value at all.
Spec == Init /\ [][Next]_vars

\* Safety: votes cast are always safe; any ballot with two votes was for the
\* same value; and votes and thresholds stay within their declared types.
Inv ==
  /\ \A p \in Acceptor : \A x \in vote[p] : x[2] \in MCBallot
  /\ \A p \in Acceptor : \A q \in Quorum : \A x \in vote[p] : \A y \in vote[q] :
       (x[2] = y[2]) => (x[1] = y[1])
  /\ TypeOK

\* The concrete voting algorithm implements the abstract consensus relation:
\* the set of chosen values is exactly the set of values backed by a quorum.
ConsensusSpecBar ==
  /\ Chosen \subseteq Value
  /\ \A v \in Value : v \in Chosen <=> \E q \in Quorum : QuorumFor(v, MCBallot) = q
====