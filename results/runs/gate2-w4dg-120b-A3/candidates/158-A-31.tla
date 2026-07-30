---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

MCAcceptor == {a1, a2, a3}
MCValue == {v1, v2}
MCQuorum == {q1, q2, q3}
q1 == {a1, a2}
q2 == {a2, a3}
q3 == {a1, a3}
MCBallot == 0..2

VARIABLES votes, thr

vars == <<votes, thr>>

VoteAt == UNION { votes[a] : a \in MCAcceptor }

TypeOK ==
  /\ votes \in [MCAcceptor -> SUBSET (MCBallot \X MCValue)]
  /\ thr \in [MCAcceptor -> {-1} \union MCBallot]

Init ==
  /\ votes = [a \in MCAcceptor |-> {}]
  /\ thr = [a \in MCAcceptor |-> -1]

SafeAt(v, b) ==
  /\ \A c \in 0..(b - 1), q \in MCQuorum :
       \E x \in q : <<c, v>> \in votes[x]

NoCrossVote(b) ==
  \A a1, a2 \in MCAcceptor :
    /\ (\E v \in MCValue : <<b, v>> \in votes[a1])
    /\ (\E v \in MCValue : <<b, v>> \in votes[a2])
    => \A v \in MCValue : (<<b, v>> \in votes[a1]) <=> (<<b, v>> \in votes[a2])

NoDouble ==
  \A a \in MCAcceptor :
    /\ \A x \in votes[a] : SafeAt(x[2], x[1])
    /\ \A b \in MCBallot : \A v \in MCValue :
         (<<b, v>> \in votes[a] /\ b < thr[a]) => FALSE

Inv == /\ TypeOK
       /\ NoCrossVote \in [MCBallot -> BOOLEAN]
       /\ NoDouble

Promisor(a, b) ==
  /\ b > thr[a]
  /\ thr' = [thr EXCEPT ![a] = b]
  /\ UNCHANGED votes

Voter(a, b, v) ==
  /\ b >= thr[a]
  /\ \A x \in votes[a] : x[1] # b
  /\ \A c \in MCAcceptor : ~(\E x \in votes[c] : x[1] = b /\ x[2] # v)
  /\ SafeAt(v, b)
  /\ votes' = [votes EXCEPT ![a] = @ \union {<<b, v>>}]
  /\ thr' = [thr EXCEPT ![a] = b]

Next ==
  \/ \E a \in MCAcceptor, b \in MCBallot : Promisor(a, b)
  \/ \E a \in MCAcceptor, b \in MCBallot, v \in MCValue : Voter(a, b, v)

Spec == Init /\ [][Next]_vars

Chosen == { v \in MCValue : \E q \in MCQuorum : \A a \in q : <<0, v>> \in votes[a] }

ConsensusSpecBar == \A q \in MCQuorum : \A a \in q : <<0, v1>> \in votes[a] => Chosen = {v1}

MCSymmetry ==
  { f \in [MCAcceptor -> MCAcceptor] :
      /\ \A q \in MCQuorum : \E r \in MCQuorum : {f[a] : a \in q} = r
      /\ \A a \in MCAcceptor : \A b \in MCAcceptor : f[a] = f[b] => a = b }
====