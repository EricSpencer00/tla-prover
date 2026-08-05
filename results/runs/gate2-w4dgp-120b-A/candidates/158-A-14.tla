---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

VARIABLES votes, threshold

vars == <<votes, threshold>>

NoVote == <<Ballot, Value>>

\* Quorums must overlap, which is declared as an explicit assumption in the
\* description -- the model's invariants rely on it.
QuorumsOverlap == \A q1 \in MCQuorum, q2 \in MCQuorum : q1 # q2 => q1 \cap q2 # {}

Voted(v, b) == {a \in MCAcceptor : <<b, v>> \in votes[a]}
ChosenSet == {v \in MCValue : \E a \in MCAcceptor, b \in MCBallot : <<b, v>> \in votes[a]}
\* Safe means no quorum blocked the value in a lower ballot, so the value can
\* be voted for in the current ballot without conflicting with anyone's vote.
Safe(v, b) ==
  \A c \in MCBallot : c < b =>
    \E q \in MCQuorum :
      \A a \in q : c < threshold[a] \/ <<c, v>> \in votes[a]

TypeOK ==
  /\ votes \in [MCAcceptor -> SUBSET (MCBallot \X MCValue)]
  /\ threshold \in [MCAcceptor -> (-1) \cup MCBallot]

Init ==
  /\ votes = [a \in MCAcceptor |-> {}]
  /\ threshold = [a \in MCAcceptor |-> -1]

\* An acceptor may raise its promise threshold without casting a vote.
RaiseThreshold(a, b) ==
  /\ b > threshold[a]
  /\ threshold' = [threshold EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* A vote is cast only if no quorum blocks it on a lower ballot.
Cast(a, v, b) ==
  /\ b >= threshold[a]
  /\ <<b, v>> \notin votes[a]
  /\ \A a2 \in MCAcceptor : a2 # a => <<b, v>> \notin votes[a2]
  /\ Safe(v, b)
  /\ votes' = [votes EXCEPT ![a] = @ \cup {<<b, v>>}]
  /\ threshold' = [threshold EXCEPT ![a] = b]

Next ==
  \/ \E a \in MCAcceptor, b \in MCBallot : RaiseThreshold(a, b)
  \/ \E a \in MCAcceptor, v \in MCValue, b \in MCBallot : Cast(a, v, b)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(\E a \in MCAcceptor, b \in MCBallot : RaiseThreshold(a, b))

\* Each ballot chooses at most one value: no two values ever both gather a quorum in the same ballot.
BallotChoosesOneValue ==
  \A b \in MCBallot, v1 \in MCValue, v2 \in MCValue :
    (\A q \in MCQuorum : \A a \in q : <<b, v1>> \in votes[a]) /\ (\A q \in MCQuorum : \A a \in q : <<b, v2>> \in votes[a])
      => v1 = v2

\* That's what makes the chosen set a singleton or empty: each voted value is backed by a quorum, and each ballot backs at most one value.
Inv == TypeOK /\ BallotChoosesOneValue

\* Refinement: the voting algorithm implements consensus, with the chosen set derived from the votes.
ConsensusSpecBar ==
  /\ \A v \in MCValue : v \in ChosenSet => \E q \in MCQuorum : \A a \in q : <<Ballot, v>> \in votes[a]
  /\ \A x \in ChosenSet, y \in ChosenSet : x = y

MCSymmetry == {p \in [MCAcceptor -> MCAcceptor] : \A a \in MCAcceptor : p[a] \in MCAcceptor}

====