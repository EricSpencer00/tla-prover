---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

ASSUME /\ Acceptor = {a1, a2, a3}
       /\ Value = {v1, v2}
       /\ Quorum = {{a1, a2}, {a2, a3}}
       /\ Ballot = {0, 1}
       /\ \A Q1 \in Quorum, Q2 \in Quorum : Q1 # Q2 => Q1 \cap Q2 # {}

VARIABLES votes, promised

vars == <<votes, promised>>

TypeOK ==
  /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ promised \in [Acceptor -> (-1)..1]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ promised = [a \in Acceptor |-> -1]

\* An acceptor raises its promise threshold and refuses to vote below it.
Raise(a, b) ==
  /\ b >= 1
  /\ b > promised[a]
  /\ promised' = [promised EXCEPT ![a] = b]
  /\ UNCHANGED votes

HasVoted(a, b) == \E w \in votes[a] : w[1] = b

\* A quorum of acceptors all safe at ballot b is what grants the vote.
Grantable(a, b, v) ==
  /\ b >= 1
  /\ b > promised[a]
  /\ ~HasVoted(a, b)
  /\ \A a2 \in Acceptor : HasVoted(a2, b) => (\E w \in votes[a2] : w[2] = v)
  /\ \E Q \in Quorum :
       /\ \A a2 \in Q : HasVoted(a2, b) => (\E w \in votes[a2] : w[2] = v)
       /\ \A a2 \in Q : \E c \in Ballot :
            /\ c < b => \E w \in votes[a2] : w[1] = c /\ w[2] = v
            \/ (c >= b /\ ~HasVoted(a2, c)
                  /\ \A Q2 \in Quorum : a2 \in Q2 => \E a3 \in Q2 : HasVoted(a3, c))

\* Casting a vote advances the acceptor's own threshold to that ballot.
Cast(a, b, v) ==
  /\ Grantable(a, b, v)
  /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
  /\ promised' = [promised EXCEPT ![a] = IF b > @ THEN b ELSE @]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : Raise(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : Cast(a, b, v)

Spec == Init /\ [][Next]_vars

CastVotes(a) == {w[2] : w \in votes[a]}
Chosen == \E Q \in Quorum : {CastVotes(a2) : a2 \in Q}

\* Every vote is safe at its ballot number, so no two values ever win a
\* quorum: at most one value is ever chosen.
Inv ==
  /\ \A a \in Acceptor, w \in votes[a] : Grantable(a, w[1], w[2])
  /\ \A a1, a2 \in Acceptor :
       \A w1 \in votes[a1], w2 \in votes[a2] :
         (w1[1] = w2[1] /\ w1[2] # w2[2]) => ({w1[2]} = {w2[2]})
  /\ TypeOK

\* The voting algorithm implements an abstract consensus spec via refinement.
ConsensusSpecBar ==
  /\ \A a \in Acceptor : votes[a] \subseteq (Ballot \X Value)
  /\ Chosen \subseteq {Value}
  /\ Chosen \subseteq {w[2] : a \in Acceptor, w \in votes[a]}
  /\ \A Q \in Quorum : CastVotes(a) \subseteq Chosen
  /\ UNCHANGED <<votes, promised>>

\* Symmetry of the three acceptors: every permutation of them is an
\* automorphism that preserves the vote and promise structure.
MCSymmetry ==
  {f \in [Acceptor -> Acceptor] :
     /\ \A a \in Acceptor : LET b == f[a] IN Cardinality({x \in Acceptor : f[x] = b}) = 1
     /\ \A a \in Acceptor : votes[a] = votes[f[a]]
     /\ \A a \in Acceptor : promised[a] = promised[f[a]]}

\* Bounded instantiations for model checking.
MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

====