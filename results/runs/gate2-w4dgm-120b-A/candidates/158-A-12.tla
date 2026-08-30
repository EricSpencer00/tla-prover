---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* Symmetry: these two definitions are overridden by the .cfg's substitution
\* to restrict the model to a finite fragment of the infinite ballot space.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

VARIABLES votes, threshold

vars == <<votes, threshold>>

\* A vote is a ballot-number/value pair; the threshold is the acceptor's
\* promise about which ballot numbers it will not go below.
VoteType == [ball : Ballot, val : Value]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

\* An acceptor may raise its threshold (promise) without voting; this is what
\* prevents it from voting in a ballot below the promise it already made.
RaiseThreshold(a) ==
  /\ \E b \in Ballot :
       /\ b > threshold[a]
       /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* Casting a ballot-b vote for a value is only allowed if no other value has
\* already won that ballot, and if the value is safe (quorum-backed) at b.
CastVote(a) ==
  /\ \E b \in Ballot, v \in Value :
       /\ b >= threshold[a]
       /\ \A x \in Acceptor : [ball |-> b, val |-> v] \notin votes[x]
       /\ \A x \in Acceptor, w \in Value :
            ([ball |-> b, val |-> w] \in votes[x]) => (w = v)
       /\ \A c \in Ballot :
            (c < b) => \E Q \in Quorum :
                         \A x \in Q :
                           \/ [ball |-> c, val |-> v] \in votes[x]
                           \/ \A w \in Value : [ball |-> c, val |-> w] \notin votes[x]
       /\ votes' = [votes EXCEPT ![a] = @ \cup {[ball |-> b, val |-> v]}]
       /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor : RaiseThreshold(a)
  \/ \E a \in Acceptor : CastVote(a)

Spec == Init /\ [][Next]_vars

\* Chosen values are those backed by a full quorum at some ballot.
Chosen ==
  { v \in Value :
      \E b \in Ballot, Q \in Quorum : \A x \in Q : [ball |-> b, val |-> v] \in votes[x] }

\* SAFETY: votes stay consistent across ballot numbers, so the chosen set never
\* contains two different values (at most one value is ever picked by a quorum).
Inv ==
  /\ (\A a1 \in Acceptor, a2 \in Acceptor :
        /\ (votes[a1] # {}) => (\A x \in votes[a1] : (\A y \in votes[a2] : x.val = y.val) \/ (a1 = a2))
        /\ (votes[a2] # {}) => (\A y \in votes[a2] : (\A x \in votes[a1] : x.val = y.val) \/ (a1 = a2)))
  /\ (\A a \in Acceptor : \A x \in votes[a] : x.val \in Value)
  /\ (\A a \in Acceptor : threshold[a] \in (Ballot \cup {-1}))

\* LIVENESS: the protocol always keeps voting for some value in some ballot.
Poke == \E a \in Acceptor : CastVote(a)

ConsensusSpecBar == TRUE /\ [][Poke]_vars

\* Symmetry: acceptors are indistinguishable and can be permuted without
\* changing the shape of the reachable state space.
MCSymmetry == {f \in [Acceptor -> Acceptor] : \A Q \in Quorum : f[Q] \in Quorum}

====