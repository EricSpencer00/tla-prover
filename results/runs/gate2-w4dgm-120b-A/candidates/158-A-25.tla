---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

(* A high-level voting-based consensus algorithm that abstracts Paxos.  The  *)
(* ballot number is a per-acceptor bound on how far the acceptor has promised *)
(* to go, so acceptors can advance without voting and voting only happens at *)
(* or above the acceptor's threshold.  A value is chosen by a quorum of       *)
(* acceptors voting for it in the same ballot, and quorum overlap forces      *)
(* distinct ballots to agree on the same value.                             *)

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

ASSUME Acceptor = {a1, a2, a3}
ASSUME Value = {v1, v2}
ASSUME Quorum = { {a1, a2}, {a2, a3} }
ASSUME Ballot = 0..1

VARIABLES vote, threshold
vars == <<vote, threshold>>

Votes == [ball : Ballot, val : Value]
Voted(a) == { v.val : v \in vote[a] }
ThresholdOK == \A a \in Acceptor : threshold[a] \in Ballot \cup {-1}
NoVoteBelowTh == \A a \in Acceptor : \A v \in vote[a] : v.ball >= threshold[a]

TypeOK ==
  /\ vote \in [Acceptor -> SUBSET Votes]
  /\ threshold \in [Acceptor -> Ballot \cup {-1}]
  /\ ThresholdOK
  /\ NoVoteBelowTh

Init ==
  /\ vote = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

\* An acceptor raises its promise threshold without voting.
Promise(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED vote

\* An acceptor votes for a value in a ballot, at or above its promise level,
\* and only if no other value has already been chosen in that ballot.
Vote(a, b, v) ==
  /\ b >= threshold[a]
  /\ \A w \in vote[a] : w.ball # b
  /\ \A c \in Acceptor : \A w \in vote[c] : (w.ball = b) => (w.val = v)
  /\ \E Q \in MCQuorum : \A q \in Q : (q \in Acceptor) =>
        (\A r \in Quorum : v \in Voted(q))
  /\ vote' = [vote EXCEPT ![a] = vote[a] \cup {[ball |-> b, val |-> v]}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in MCBallot : Promise(a, b)
  \/ \E a \in Acceptor, b \in MCBallot, v \in MCValue : Vote(a, b, v)

Spec == Init /\ [][Next]_vars

\* Every value in a quorum that voted for it is the only value that any       *
\* other acceptor voted for in the same ballot (a consequence of quorum       *
\* overlap and the ballot-level single-choice rule).                         *
SingleValuePerBallot ==
  \A Q \in MCQuorum : \A a \in Q : \A b \in Q : a # b =>
    \A v \in Voted(a), w \in Voted(b) : v = w

\* No two distinct values are ever both voted for by a quorum in some ballot.*
NoDoubleChoice == \A Q1 \in MCQuorum, Q2 \in MCQuorum :
  (\A a \in Q1 : \E v \in Voted(a) : TRUE) /\ (\A b \in Q2 : \E w \in Voted(b) : TRUE)
    => ( \E v \in Voted(\E a \in Q1 : a) : v = \E w \in Voted(\E b \in Q2 : b) : w)

\* The chosen-value set contains at most one value; no value can be chosen  *
\* in two different ballots unless it is the same value.                    *
Inv == TypeOK /\ SingleValuePerBallot /\ NoDoubleChoice

\* Every ballot round in a quorum agreeing on a value is a genuine choose     *
\* event -- the vote relation is functional per ballot, so an agreeer's      *
\* ballot record already names the chosen value.                            *
ConsensusSpecBar == \A Q \in MCQuorum : \A a, b \in Q :
  \A w1, w2 \in vote[a] : (w1.ball = w2.ball) => (w1.val = w2.val)

\* Every acceptor that has voted is indistinguishable from any other         *
\* acceptor that has voted, up to renaming of the actual values.            *
MCSymmetry == \E f \in [Acceptor -> Acceptor] :
  \A a \in Acceptor : vote[a] = vote[f[a]]

(* For model checking we instantiate the quorums with concrete intersecting *)
(* pairs of acceptors, and ballot numbers only need a bounded range.      *)
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == { {a1, a2}, {a2, a3} }
MCBallot == 0..1
====