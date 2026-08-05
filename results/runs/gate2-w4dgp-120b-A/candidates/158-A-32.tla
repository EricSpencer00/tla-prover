---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

Vote == [ball : Ballot, val : Value]
Promised == [prt : Acceptor, ball : Ballot]

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

NoBallot == CHOOSE b \in Ballot : \A c \in Ballot : c >= b
NoVal == CHOOSE v \in Value : \A w \in Value : w = v

VARIABLES cast, promised

vars == <<cast, promised>>

QuorumIntersects(q1, q2) == \E x \in q1 : x \in q2
QuorumsIntersect == \A q1, q2 \in MCQuorum : QuorumIntersects(q1, q2)

TypeOK ==
  /\ cast \in [MCAcceptor -> SUBSET [ball : MCBallot, val : MCValue]]
  /\ promised \in [MCAcceptor -> MCBallot \cup {NoBallot}]

Init ==
  /\ cast = [a \in MCAcceptor |-> {}]
  /\ promised = [a \in MCAcceptor |-> NoBallot]

Voted(a) == {c.val : c \in cast[a]}
SetVoted == {a.val : a \in UNION cast}

AtMostOneValueQ == (\A q \in MCQuorum : \A a \in q : \E x \in cast[a] : TRUE) => SetVoted = MCVote

SafeAtBallot(b, v) ==
  \A c \in {x \in Ballot : x < b} :
    \E qq \in MCQuorum :
      \A a \in qq : (\E x \in cast[a] : x.val = v /\ x.ball = c) \/ (promised[a] # NoBallot /\ promised[a] > c)

VoteSafe ==
  \A a \in MCAcceptor : \A x \in cast[a] : SafeAtBallot(x.ball, x.val)

QuorumForValue(v) == {q \in MCQuorum : \A a \in q : \E x \in cast[a] : x.val = v}
Chosen == {v \in MCValue : QuorumForValue(v) # {}}

Consistent == \A v1 \in Chosen, v2 \in Chosen : v1 = v2

OneBallotPerValue == (\A a \in MCAcceptor, x \in cast[a] : \A b \in cast[a] : x.ball = b.ball => x.val = b.val) => SetVoted = MCValue
RefinesConsensus == Consistent /\ OneBallotPerValue

Next ==
  \/ \E a \in MCAcceptor, b \in MCBallot :
       /\ (promised[a] = NoBallot \/ b > promised[a])
       /\ promised' = [promised EXCEPT ![a] = b]
       /\ UNCHANGED cast
  \/ \E a \in MCAcceptor, b \in MCBallot, v \in MCValue :
       /\ (promised[a] = NoBallot \/ b >= promised[a])
       /\ \A x \in cast[a] : x.ball # b
       /\ \A x \in UNION {cast[x] : x \in MCAcceptor} : (x.ball = b /\ x.val # v) = FALSE
       /\ \E q \in MCQuorum : \A x \in q : SafeAtBallot(b, v)
       /\ cast' = [cast EXCEPT ![a] = @ \cup {[ball |-> b, val |-> v]}]
       /\ promised' = [promised EXCEPT ![a] = b]

Spec == Init /\ [][Next]_vars

Inv == TypeOK /\ VoteSafe

====