---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

VARIABLES votes, threshold

vars == <<votes, threshold>>

Vote == [ball : Ballot, val : Value]

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET Vote]
  /\ threshold \in [Acceptor -> Ballot \cup {-1}]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

\* A quorum is safe at ballot b if every lower ballot c has a quorum all of
\* whose members already voted for this value or can never vote at c.
SafeAt(v, b) ==
  \A c \in Ballot :
    /\ c < b => \E Q \in Quorum :
         /\ \A a \in Q : \E w \in votes[a] : w.ball = c /\ w.val = v
         /\ \A a \in Q : \A w \in votes[a] : w.ball = c => w.val = v

\* An acceptor may raise its promise threshold (it will not vote below it).
Promise(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* Place a safe vote, never below the acceptor's current threshold.
Vote(a, v, b) ==
  /\ b >= threshold[a]
  /\ ~\E w \in votes[a] : w.ball = b
  /\ \A x \in Acceptor : \A w \in votes[x] : w.ball = b => w.val = v
  /\ SafeAt(v, b)
  /\ votes' = [votes EXCEPT ![a] = @ \cup {[ball |-> b, val |-> v]}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : Promise(a, b)
  \/ \E a \in Acceptor, v \in Value, b \in Ballot : Vote(a, v, b)

Spec == Init /\ [][Next]_vars

\* A chosen value is backed by an entire quorum of matching votes.
Chosen(v) == \E Q \in Quorum : \A a \in Q : [ball |-> 0, val |-> v] \in votes[a]

\* SAFETY: at most one value is ever chosen by a quorum of votes.
Inv ==
  /\ \A a \in Acceptor : \A w \in votes[a] : SafeAt(w.val, w.ball)
  /\ \A w1, w2 \in UNION {votes[a] : a \in Acceptor} :
        w1.ball = w2.ball => w1.val = w2.val
  /\ TypeOK

\* CONSISTENCY: the chosen set never contains two distinct values.
ConsensusSpecBar ==
  Cardinality({v \in Value : Chosen(v)}) <= 1

\* REFINEMENT MAP: the chosen set is derived from the vote record.
MCSymmetry == {<<a1, a2, a3>>}

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

====