---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

ASSUME Acceptor = {a1, a2, a3}
ASSUME Value = {v1, v2}
ASSUME Ballot = Nat
ASSUME Quorum = {Q1, Q2, Q3}
ASSUME Q1 = {a1, a2}
ASSUME Q2 = {a2, a3}
ASSUME Q3 = {a1, a3}

VARIABLES votes, promised
vars == <<votes, promised>>

QuorumIntersects == \A Q, R \in Quorum : Q \cap R # {}

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ promised = [a \in Acceptor |-> -1]

RaiseThreshold(a, b) ==
  /\ b \in Ballot
  /\ b > promised[a]
  /\ promised' = [promised EXCEPT ![a] = b]
  /\ UNCHANGED votes

Voted(a, b, v) == <<b, v>> \in votes[a]

ValueSafe(v, b) ==
  /\ \A c \in Ballot : c < b => \E Q \in Quorum : \A a \in Q : Voted(a, c, v) \/ (\A w \in Value : ~ Voted(a, c, w))
  /\ \A c \in Ballot : c < b => \A a \in Acceptor : Voted(a, c, v) \/ (\A w \in Value : ~ Voted(a, c, w))

CastVote(a, b, v) ==
  /\ b \in Ballot
  /\ b >= promised[a]
  /\ \A w \in Value : ~ Voted(a, b, w)
  /\ \A d \in Acceptor : (\E x \in Value : Voted(d, b, x)) => v = (CHOOSE x \in Value : Voted(d, b, x))
  /\ ValueSafe(v, b)
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<b, v>>}]
  /\ promised' = [promised EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : RaiseThreshold(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : CastVote(a, b, v)

Spec == Init /\ [][Next]_vars

Chosen == {w \in Value : \E Q \in Quorum : \A a \in Q : Voted(a, CHOOSE b \in Ballot : <<b, w>> \in votes[a])}

VoteSafety ==
  /\ \A a \in Acceptor : \A z \in votes[a] : ValueSafe(z[2], z[1])
  /\ \A a, b \in Acceptor, x, y \in Ballot : (Voted(a, x, v1) /\ Voted(b, y, v2)) => v1 = v2
  /\ \A a \in Acceptor : votes[a] \subseteq ({b \in Ballot : b >= promised[a]} \X Value)

Inv == VoteSafety

ConsensusSpecBar == QuorumIntersects /\ Inv

DefinePermutation(f) ==
  /\ \A x \in Acceptor : f[x] \in Acceptor
  /\ \A x, y \in Acceptor : f[x] = f[y] => x = y
  /\ \A y \in Acceptor : \E x \in Acceptor : f[x] = y
  /\ \A x \in Value : f[x] = x
  /\ \A x \in Ballot : f[x] = x
  /\ \A x \in Quorum : f[x] = x

MCSymmetry == {f \in [Acceptor -> Acceptor] : DefinePermutation(f)}

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == {0, 1}

====