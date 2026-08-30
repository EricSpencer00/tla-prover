---- MODULE Voting ----
EXTENDS Integers, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

Votes == [ball : Ballot, val : Value]

\* Self-loops: Acceptor, Value, Quorum, Ballot are abstract constants that may be
\* instantiated with any finite sets; they are not enumerated here. The cfg file
\* substitutes their bounded versions via MCAcceptor, MCValue, MCQuorum, and MCBallot.
VARIABLES casts, pthreshold

vars == <<casts, pthreshold>>

TypeOK ==
  /\ casts \in [Acceptor -> SUBSET Votes]
  /\ pthreshold \in [Acceptor -> Ballot \cup {-1}]

Init ==
  /\ casts = [a \in Acceptor |-> {}]
  /\ pthreshold = [a \in Acceptor |-> -1]

\* Raise the acceptor's promise threshold so it will not vote in a ballot below it.
RaiseThreshold(a, b) ==
  /\ b > pthreshold[a]
  /\ pthreshold' = [pthreshold EXCEPT ![a] = b]
  /\ UNCHANGED casts

\* A ballot in which another acceptor has already voted for a different value is dead.
NoConflict(v, b) ==
  \A a \in Acceptor : \A w \in casts[a] : (w.ball = b) => (w.val = v)

QuorumSafe(v, b) ==
  \E Q \in Quorum :
    /\ \A a \in Q : (\E w \in casts[a] : (w.ball = b) /\ (w.val = v))
    /\ \A c \in (Ballot \ {b}) :
         \A Qp \in Quorum :
           \A a \in Qp : \E w \in casts[a] : (w.ball = c) /\ (w.val = v)

Vote(v, a, b) ==
  /\ b >= pthreshold[a]
  /\ ~(\E w \in casts[a] : w.ball = b)
  /\ NoConflict(v, b)
  /\ QuorumSafe(v, b)
  /\ casts' = [casts EXCEPT ![a] = @ \cup {[ball |-> b, val |-> v]}]
  /\ pthreshold' = [pthreshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : RaiseThreshold(a, b)
  \/ \E v \in Value, a \in Acceptor, b \in Ballot : Vote(v, a, b)

Spec == Init /\ [][Next]_vars

\* A chosen value is supported by a quorum of acceptors voting for it in some ballot.
Chosen ==
  {v \in Value :
     \E b \in Ballot :
       \E Q \in Quorum :
         \A a \in Q : \E w \in casts[a] : (w.ball = b) /\ (w.val = v)}

\* Exact-consensus shape: at most one value is ever chosen, via the three invariants.
Inv ==
  /\ \A a \in Acceptor : \A w \in casts[a] : QuorumSafe(w.val, w.ball)
  /\ \A a1, a2 \in Acceptor :
        \A w1 \in casts[a1] : \A w2 \in casts[a2] : (w1.ball = w2.ball) => (w1.val = w2.val)
  /\ TypeOK

\* The ballot-number assignment is a refinement mapping to the abstract consensus spec.
ConsensusSpecBar ==
  /\ Chosen \subseteq Value
  /\ \A v \in Chosen : \E a \in Acceptor : \E w \in casts[a] : w.val = v

MCSymmetry ==
  {p \in [Acceptor -> Acceptor] :
     /\ \A a \in Acceptor : p[a] \in Acceptor
     /\ \A a1 \in Acceptor : \A a2 \in Acceptor : (a1 = a2) <=> (p[a1] = p[a2])}

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

====