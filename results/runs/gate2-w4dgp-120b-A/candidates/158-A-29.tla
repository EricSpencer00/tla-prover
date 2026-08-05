---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* A quorum is a set of acceptors; the overlap property required by the
\* Consistency proof is declared here as an INVARIANT rather than baked
\* into the type, so the same quorums can be instantiated with or without
\* overlap (the first is safe, the second is not, and the proof fails).
QuorumsOverlap == \A q1, q2 \in Quorum : q1 # q2 => q1 \cap q2 # {}

VARIABLES cast, promised

vars == <<cast, promised>>

Voters == [ballot : Ballot, value : Value, who : Acceptor]
Votes(a) == {v \in cast : v.who = a}

TypeOK ==
  /\ cast \subseteq [ballot : Ballot, value : Value, who : Acceptor]
  /\ promised \in [Acceptor -> (-1 :> Ballot)]

Init ==
  /\ cast = {}
  /\ promised = [a \in Acceptor |-> -1]

\* A quorum of acceptors all find the value safe at the ballot number.
SafeAt(v, b) ==
  \A c \in Ballot :
    /\ c <= b
    /\ \E q \in Quorum :
         \A a \in q :
           \/ \E w \in Votes(a) : w.ballot = c /\ w.value = v
           \/ promised[a] > c

\* An acceptor may raise its participation threshold without voting.
RaiseThreshold(a, b) ==
  /\ b > promised[a]
  /\ promised' = [promised EXCEPT ![a] = b]
  /\ UNCHANGED cast

\* An acceptor casts a vote; the ballot must not be below its threshold,
\* it must not have already voted in that ballot, and no other acceptor
\* may have voted for a different value in that same ballot.
CastVote(a, v, b) ==
  /\ b >= promised[a]
  /\ \A w \in Votes(a) : w.ballot # b
  /\ \A w \in cast : w.ballot = b => w.value = v
  /\ SafeAt(v, b)
  /\ cast' = cast \cup {[ballot |-> b, value |-> v, who |-> a]}
  /\ promised' = [promised EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor, b \in Ballot : RaiseThreshold(a, b)
  \/ \E a \in Acceptor, v \in Value, b \in Ballot : CastVote(a, v, b)

Spec == Init /\ [][Next]_vars

Inv ==
  /\ TypeOK
  /\ \A v \in Value, b \in Ballot :
       (\E a \in Acceptor : [ballot |-> b, value |-> v, who |-> a] \in cast)
         => SafeAt(v, b)
  /\ \A a, b \in Acceptor : (\E v \in Value, c \in Ballot :
        [ballot |-> c, value |-> v, who |-> a] \in cast
          /\ [ballot |-> c, value |-> v, who |-> b] \in cast) => v = w

\* The chosen set is derived from the votes and must stay single-valued.
ConsensusSpecBar ==
  \A b \in Ballot :
    \A v \in Value, q \in Quorum :
      (\A a \in q : [ballot |-> b, value |-> v, who |-> a] \in cast) ~>
        (\A w \in Value : (\A a \in q : [ballot |-> b, value |-> w, who |-> a] \in cast) => w = v)
  /\ \A q \in Quorum : (\A a \in q : a \in Acceptor) => \A a \in q : a \in cast

MCAcceptor == Acceptor
MCValue == Value
MCQuorum == Quorum
MCBallot == Ballot

MCSymmetry ==
  {f \in [Acceptor -> Acceptor] : f = [a \in Acceptor |-> a]}

====