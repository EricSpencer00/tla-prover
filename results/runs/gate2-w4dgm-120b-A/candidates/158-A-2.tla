---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

VARIABLES votes, thresh

vars == <<votes, thresh>>

Quorums == [ Q1 |-> {a1, a2}, Q2 |-> {a2, a3}, Q3 |-> {a1, a3} ]

TypeOK ==
  /\ votes \in [ MCAcceptor -> SUBSET (MCBallot \X MCValue) ]
  /\ thresh \in [ MCAcceptor -> MCBallot \cup { -1 } ]

Init ==
  /\ votes = [ a \in MCAcceptor |-> {} ]
  /\ thresh = [ a \in MCAcceptor |-> -1 ]

Promised(a, b) == b >= thresh[a]

HasVotedIn(a, b) == \E x \in votes[a] : x[1] = b

SafeAt(v, b) ==
  \A c \in 0..b :
    \E Q \in MCQuorum :
      \A a \in Q :
        \/ <<c, v>> \in votes[a]
        \/ \E x \in votes[a] : x[1] = c
        \/ \E x \in votes[a] : x[1] > c

AllVotedIn(a, b) == \A c \in 0..b : HasVotedIn(a, c)

Vote(a, b, v) ==
  /\ b \in MCBallot
  /\ Promised(a, b)
  /\ ~HasVotedIn(a, b)
  /\ \A c \in 0..b : \A d \in MCAcceptor :
        (<<c, v>> \in votes[d]) => (c = b \/ d = a)
  /\ SafeAt(v, b)
  /\ votes' = [ votes EXCEPT ![a] = @ \cup { <<b, v>> } ]
  /\ thresh' = [ thresh EXCEPT ![a] = b ]

RaiseThresh(a, b) ==
  /\ b \in MCBallot
  /\ b > thresh[a]
  /\ thresh' = [ thresh EXCEPT ![a] = b ]
  /\ UNCHANGED votes

Next ==
  \/ \E a \in MCAcceptor, b \in MCBallot, v \in MCValue : Vote(a, b, v)
  \/ \E a \in MCAcceptor, b \in MCBallot : RaiseThresh(a, b)

Spec == Init /\ [][Next]_vars

Chosen(v) == \E Q \in MCQuorum : \A a \in Q : <<0, v>> \in votes[a]

ChosenCount <= 1 == \A v1, v2 \in MCValue : (Chosen(v1) /\ Chosen(v2)) => v1 = v2

Inv ==
  /\ \A a \in MCAcceptor : \A x \in votes[a] : SafeAt(x[2], x[1])
  /\ \A a1 \in MCAcceptor, a2 \in MCAcceptor :
        \A v1, v2 \in MCValue, b \in MCBallot :
          (<<b, v1>> \in votes[a1] /\ <<b, v2>> \in votes[a2]) => v1 = v2
  /\ \A a \in MCAcceptor : AllVotedIn(a, thresh[a])
  /\ TypeOK

\* The voting algorithm implements consensus: the derived chosen set contains
\* at most one value, and the votes are type-consistent. The symmetry
\* condition holds under any permutation of acceptors, ballots, or values.
ConsensusSpecBar == ChosenCount <= 1

BeyondBallots == CHOOSE b \in MCBallot :
  \A c \in MCBallot : c <= b /\ \A a \in MCAcceptor : thresh[a] <= b

MCSymmetry ==
  /\ \A f \in [ MCAcceptor -> MCAcceptor ] :
        /\ \A a \in MCAcceptor : f[a] \in MCAcceptor
        /\ \A a1 \in MCAcceptor, a2 \in MCAcceptor : f[a1] = f[a2] => a1 = a2
        /\ \A a \in MCAcceptor : votes' = [ votes EXCEPT ![f[a]] = @ ]
  /\ \A g \in [ MCValue -> MCValue ] :
        /\ \A v \in MCValue : g[v] \in MCValue
        /\ \A v1 \in MCValue, v2 \in MCValue : g[v1] = g[v2] => v1 = v2
        /\ \A a \in MCAcceptor, x \in votes[a] :
              votes' = [ votes EXCEPT ![a] = ( @ \ { x } ) \cup { <<x[1], g[x[2]]>> } ]
  /\ \A h \in [ MCBallot -> MCBallot ] :
        /\ \A b \in MCBallot : h[b] \in MCBallot
        /\ \A b1 \in MCBallot, b2 \in MCBallot : h[b1] = h[b2] => b1 = b2
        /\ \A a \in MCAcceptor, x \in votes[a] :
              votes' = [ votes EXCEPT ![a] = ( @ \ { x } ) \cup { <<h[x[1]], x[2]>> } ]
        /\ thresh' = [ thresh EXCEPT ![a] = h[thresh[a]] ]
  /\ UNCHANGED <<votes, thresh>>

====