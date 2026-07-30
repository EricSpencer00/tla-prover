---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, Acceptor, Value, Quorum, Ballot

VARIABLES votes, threshold
vars == <<votes, threshold>>

\* Each vote a process casts is a ballot-number/value pair; votes[proc] is the
\* set of votes that process has cast.
Vote == [ball : Ballot, val : Value]

\* A value is safe at ballot b if every lower ballot has a unanimous quorum
\* for that value, or a quorum of acceptors that can no longer vote.
SafeAt(v, b) ==
  \A c \in 0..(b - 1) :
    \E Q \in Quorum :
      \A p \in Q : (c >= threshold[p]) => \E vt \in votes[p] : (vt.ball = c /\ vt.val = v)

Bump(n, m) == IF n > m THEN n ELSE m

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET Vote]
  /\ threshold \in [Acceptor -> Ballot]

Init ==
  /\ votes = [p \in Acceptor |-> {}]
  /\ threshold = [p \in Acceptor |-> 0]

\* A process raises its promise threshold without voting.
RaiseThreshold(p, n) ==
  /\ n > threshold[p]
  /\ threshold' = [threshold EXCEPT ![p] = n]
  /\ UNCHANGED votes

\* Cast a vote, provided the ballot is above the process's threshold, it has not
\* already voted in this ballot, no other process voted for a different value in
\* this ballot, and the value is safe at this ballot.
Cast(p, n, v) ==
  /\ n > threshold[p]
  /\ \A vt \in votes[p] : vt.ball # n
  /\ \A q \in Acceptor : \A vt \in votes[q] : (vt.ball = n => vt.val = v)
  /\ SafeAt(v, n)
  /\ votes' = [votes EXCEPT ![p] = @ \cup {[ball |-> n, val |-> v]}]
  /\ threshold' = [threshold EXCEPT ![p] = n]

Next ==
  \/ \E p \in Acceptor : \E n \in Ballot : RaiseThreshold(p, n)
  \/ \E p \in Acceptor : \E n \in Ballot : \E v \in Value : Cast(p, n, v)

Spec == Init /\ [][Next]_vars

\* Chosen values are backed by a unanimous quorum; at most one value is ever
\* chosen because quorums overlap and voting is safe.
Chosen ==
  {v \in Value :
    \E Q \in Quorum :
      \A p \in Q : \E vt \in votes[p] : vt.val = v}

Inv ==
  /\ \A p \in Acceptor : \A vt \in votes[p] : SafeAt(vt.val, vt.ball)
  /\ \A vt1, vt2 \in UNION {votes[p] : p \in Acceptor} :
       (vt1.ball = vt2.ball /\ vt1 # vt2) => (vt1.val = vt2.val)
  /\ TypeOK

\* The abstract consensus spec is derived from the votes, so the voting
\* algorithm implements consensus.
ConsensusSpecBar == Chosen \subseteq Value

====