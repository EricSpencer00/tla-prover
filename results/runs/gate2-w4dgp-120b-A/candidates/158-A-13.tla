---- MODULE Voting ----
EXTENDS Naturals, FiniteSets

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

VARIABLES votes, promised

vars == <<votes, promised>>

Quorums == {s \in SUBSET Acceptor : Cardinality(s) >= 2}

\* The chosen set is derived from the votes that actually form a quorum in one
\* ballot; each vote is a pair of a ballot number and a value.
Chosen == {p[2] : p \in {w \in votes : \E q \in Quorums : q \subseteq votes[w[1]]}}

Cast(a, b, v) == <<a, b, v>>

TypeOK ==
  /\ votes \subseteq [Acceptor -> [Ballot -> Value]]
  /\ promised \in [Acceptor -> -1..(Ballot - 1)]

Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ promised = [a \in Acceptor |-> -1]

\* An acceptor may raise its promise threshold; this is the only way a
\* participant decides to stop taking part in lower-numbered ballots.
Promise(a, b) ==
  /\ b > promised[a]
  /\ promised' = [promised EXCEPT ![a] = b]
  /\ UNCHANGED votes

\* An acceptor votes for a value in a ballot only if no other value has already
\* been voted for in that ballot, and only if a quorum can certify the value as
\* safe at that ballot number. Casting a vote also raises the acceptor's
\* threshold to the ballot it just voted in.
CastVote(a, b, v) ==
  /\ b >= promised[a]
  /\ \A w \in votes[a] : w[1] < b
  /\ \A w \in votes[a] : w[2] # v => w[1] # b
  /\ \A x \in Acceptor : \A w \in votes[x] : w[2] # v => w[1] # b
  /\ \E q \in Quorums :
       \A c \in 0..(b - 1) : \A x \in q :
         \E w \in votes[x] :
           (w[1] = c /\ w[2] = v) \/ (c > promised[x] /\ promises[x] >= b)
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {Cast(a, b, v)}]
  /\ promised' = [promised EXCEPT ![a] = b]

Next ==
  \/ \E a \in Acceptor : \E b \in Ballot : Promise(a, b)
  \/ \E a \in Acceptor : \E b \in Ballot : \E v \in Value : CastVote(a, b, v)

Spec == Init /\ [][Next]_vars

\* Safety: at most one value is ever chosen by a quorum of acceptors.
Inv == Cardinality(Chosen) <= 1

\* The voting algorithm implements the abstract consensus spec, where a value
\* is chosen once a quorum votes for it in some ballot.
ConsensusSpecBar == Chosen \subseteq {v \in Value :
    \E b \in Ballot : \E q \in Quorums : q \subseteq votes[b] /\ votes[b] = {v}}

\* Symmetry over acceptors: any permutation of the acceptors yields a
\* behavior equivalent to the original, since no acceptor is privileged.
MCSymmetry ==
  {f \in [Acceptor -> Acceptor] : \A x \in Acceptor : f[x] = x}

\* Bounded versions for model checking (used by the .cfg substitution):
MCAcceptor == {a1, a2, a3}
MCValue == {v1, v2}
MCQuorum == {q \in SUBSET {a1, a2, a3} : Cardinality(q) >= 2}
MCBallot == 2

====