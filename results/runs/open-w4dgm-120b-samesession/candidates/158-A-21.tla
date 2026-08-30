---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

(* The set of quorum sets that satisfy the overlap property (a+2a3 = a2, a+2a1 *)
(* is a necessary assumption rather than a derived fact).                     *)

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* Vote: an acceptor's ballot-numbered vote for a value. Quorum: a set of
\* acceptors that can safely vote together (overlap is a model assumption).
Vote == [ball : Ballot, val : Value]
QuorumSig == [members : Acceptor, val : Value, ball : Ballot]

VARIABLES votes, threshold
vars == <<votes, threshold>>

\* SAFETY PROPERTY: a chosen value is backed by a quorum that voted for it in
\* some ballot. COHERENCE PROPERTY: the abstract occupancy relation between
\* values and quorums stays consistent with the concrete votes.
Spec == Spec /\ PropDef /\ Coherent

\* SAFETY PROPERTY: at most one value per ballot, every vote safe, no
\* out-of-range or out-of-turn vote; COHERENCE PROPERTY: QuorumVoter matches
\* the votes cast, and every quorum that votes really does vote for its value.
Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

\* The quorum-existence part of a vote is checked here rather than held in an
\* auxilliary variable, so the silent quorum-assumption failure is always
\* visible -- this is what makes the failure a visible safety violation.
VoteValue(a, v, b) ==
  /\ b >= threshold[a]
  /\ \A c \in Ballot : (c < b) => (\E q \in MCQuorum : q.ball = c)
  /\ \A c \in votes[a] : c.ball # b
  /\ (\A c \in Acceptor : \A d \in votes[c] : (d.ball = b => d.val = v)
  /\ \E q \in MCQuorum : q.ball = b /\ q.val = v /\ a \in q.members
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {[ball |-> b, val |-> v]}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

\* A quorum-assumption failure that is merely hidden would not show up as a
\* safety violation here, which is exactly why the check is embedded above.
Promised(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

Next == (\E a \in Acceptor, v \in MCValue, b \in MCBallot : VoteValue(a, v, b))
        \/ (\E a \in Acceptor, b \in MCBallot : Promised(a, b))

\* A chosen value must be backed by a quorum of real votes in some ballot.
Inv ==
  /\ (\A q \in MCQuorum : (\A a \in q.members : [ball |-> q.ball, val |-> q.val] \in votes[a])
  /\ (\A a \in Acceptor : \A c1, c2 \in votes[a] : c1.ball = c2.ball => c1.val = c2.val
  /\ (\A b \in Ballot :
        (\A c \in votes : c.ball < b => (\E q \in MCQuorum : q.ball = c.ball /\ q.val = c.val))
  /\ \A a \in Acceptor : threshold[a] \in Ballot

\* The quorum set itself is exactly the occupancy relation's range; a quorum
\* that voted for a value is in the range, and every range element voted.
\* This is the per-quorum side of the back-and-forth pair with each vote.
Coherent ==
  /\ \A q \in MCQuorum : \E a \in q.members : [ball |-> q.ball, val |-> q.val] \in votes[a]
  /\ \A a \in Acceptor : \A c \in votes[a] :
        \E q \in MCQuorum : q.ball = c.ball /\ q.val = c.val /\ a \in q.members

\* The ballot numbers in play are bounded for model checking (not for the
\* real protocol); they are unbounded in the system being modeled.
\* The quorum set is a fresh constant in each run, chosen to satisfy overlap.
ConsensusSpecBar == ConsensusSpec /\ Agreement

\* The concrete vote set is a faithful implementation of the abstract
\* occupancy bookkeeping: the two sides reflect each other exactly.
ConsensusSpec ==
  /\ QuorumVoter \in [MCQuorum -> Acceptor]
  /\ \A q \in MCQuorum : [ball |-> q.ball, val |-> q.val] \in votes[QuorumVoter[q]]
  /\ \A a \in Acceptor : \A c \in votes[a] :
       (\E q \in MCQuorum : q.ball = c.ball /\ q.val = c.val /\ QuorumVoter[q] = a)
  /\ \A q1, q2 \in MCQuorum : q1.ball = q2.ball => q1.val = q2.val

\* At most one value per ballot is what keeps the system from choosing two
\* different values in different ballots, which is more than just
\* "the two values disagree at some ballot".
Agreement == \A q1, q2 \in MCQuorum : q1.ball = q2.ball => q1.val = q2.val

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot
====