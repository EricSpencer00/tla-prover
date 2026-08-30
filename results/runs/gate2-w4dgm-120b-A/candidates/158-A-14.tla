---- MODULE Voting ----
EXTENDS Naturals

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

Vote == [ball: Ballot, val: Value]

VARIABLES cast, threshold

vars == <<cast, threshold>>

UNION(x) == {y \in x : y}
QuorumMember(v) == \E Q \in Quorum : v \in Q

RECURSIVE Tally(_, _)
Tally(f, S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] \cup Tally(f, S \ {x})

VotersFor(b, v) == Tally(cast, {a \in Acceptor : \E c \in cast[a] : c.ball = b /\ c.val = v})

TypeOK ==
  /\ cast \in [Acceptor -> SUBSET Vote]
  /\ threshold \in [Acceptor -> {-1} \cup Ballot]

OnlySafeVotesCast ==
  \A a \in Acceptor : \A c \in cast[a] :
    /\ c.ball \in Ballot
    /\ c.val \in Value
    /\ \A b \in Ballot : b < c.ball => \E Q \in Quorum :
         \A m \in Q : QuorumMember(m) => (b \in VotersFor(b, c.val) \cup \{m\})

OneValuePerBallot ==
  \A b \in Ballot : \A v, w \in Value :
    (v # w /\ \E Q1, Q2 \in Quorum :
        Q1 \subseteq VotersFor(b, v) /\ Q2 \subseteq VotersFor(b, w)) => FALSE

Inv == /\ TypeOK /\ OnlySafeVotesCast /\ OneValuePerBallot

Init ==
  /\ cast = [a \in Acceptor |-> {}]
  /\ threshold = [a \in Acceptor |-> -1]

SetThreshold(a, n) ==
  /\ n > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = n]
  /\ UNCHANGED cast

Vote(a, v, n) ==
  /\ n \in Ballot
  /\ n >= threshold[a]
  /\ \A c \in cast[a] : c.ball # n
  /\ \A b \in Ballot : b < n => \E Q \in Quorum :
       \A m \in Q : QuorumMember(m) => (b \in VotersFor(b, v) \cup {m})
  /\ \A w \in Value \ {v} : ~\E Q \in Quorum : Q \subseteq VotersFor(n, w)
  /\ cast' = [cast EXCEPT ![a] = cast[a] \cup {[ball |-> n, val |-> v]}]
  /\ threshold' = [threshold EXCEPT ![a] = n]

Next ==
  \E a \in Acceptor : \E n \in Ballot : SetThreshold(a, n)
  \/ \E a \in Acceptor, v \in Value, n \in Ballot : Vote(a, v, n)

Spec == Init /\ [][Next]_vars

Chosen == UNION {VotersFor(b, v) : b \in Ballot, v \in Value}

ConsensusSpecBar == {<<b, v>> : v \in Value /\ b \in Ballot /\ QuorumMember(b)} \subseteq Chosen

MCSymmetry ==
  {f \in [Acceptor -> Acceptor] : \A Q \in Quorum : f[Q] \in Quorum}

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

====