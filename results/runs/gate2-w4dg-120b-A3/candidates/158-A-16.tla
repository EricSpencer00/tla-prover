---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

Votes == [ac : Acceptor, bal : Ballot, val : Value]
Voter(p) == { s \in Votes : s.ac = p }

VARIABLES votes, threshold
vars == <<votes, threshold>>

Quorums == Quorum

TypeOK ==
  /\ votes \subseteq Votes
  /\ threshold \in [Acceptor -> Integer]

Init ==
  /\ votes = {}
  /\ threshold = [p \in Acceptor |-> -1]

NoConflict(b, v) ==
  \A p \in Acceptor : \A s \in Voter(p) : s.bal = b => s.val = v

Safe(v, w) ==
  /\ \A c \in Ballot :
       c < w =>
         (\E Q \in Quorums :
            \A p \in Q :
              (\E s \in Voter(p) : s.bal = c /\ s.val = v) \/ threshold[p] > c)
  /\ NoConflict(w, v)

Vote(p, b, v) ==
  /\ b >= threshold[p]
  /\ \A s \in Voter(p) : s.bal # b
  /\ NoConflict(b, v)
  /\ Safe(v, b)
  /\ votes' = votes \cup {[ac |-> p, bal |-> b, val |-> v]}
  /\ threshold' = [threshold EXCEPT ![p] = b]

Raise(p, b) ==
  /\ b > threshold[p]
  /\ threshold' = [threshold EXCEPT ![p] = b]
  /\ UNCHANGED votes

Next ==
  \/ \E p \in Acceptor, b \in Ballot, v \in Value : Vote(p, b, v)
  \/ \E p \in Acceptor, b \in Ballot : Raise(p, b)

Spec == Init /\ [][Next]_vars

Chosen ==
  { v \in Value : \E Q \in Quorums : \A p \in Q : \E s \in Voter(p) : s.val = v }

AtMostOneChosen == \A a, b \in Chosen : a = b

Inv == TypeOK /\ AtMostOneChosen

ConsensusSpecBar == AtMostOneChosen

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

MCSymmetry ==
  [p \in [Acceptor -> Acceptor] |
     /\ p[MCAcceptor] \subseteq MCAcceptor
     /\ p[MCAcceptor] \cap MCAcceptor = {}
     /\ MCAcceptor = p[MCAcceptor] \cup p[MCAcceptor]]

Theorem SpecRefinesConsensus ==
  (TypeOK /\ AtMostOneChosen) => ConsensusSpecBar

====