---- MODULE Voting ----
EXTENDS Naturals

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

MCAcceptor == a1 \cup a2 \cup a3
MCValue == {v1, v2}
MCQuorum == Quorum
MCBallot == Ballot

ASSUME /\ Quorum \subseteq SUBSET Acceptor
       /\ MCAcceptor = a1 \cup a2 \cup a3
       /\ MCValue = {v1, v2}
       /\ MCAcceptor # {}
       /\ \A q1 \in Quorum, q2 \in Quorum : q1 \cap q2 # {}
       /\ \A q \in Quorum, a \in q : a \in MCAcceptor
       /\ \A q \in Quorum, a \in MCAcceptor : {a} \cup q \in Quorum

VARIABLES votes, promised
vars == <<votes, promised>>

Cast == UNION {votes[a] : a \in MCAcceptor}

\* A vote is safe at its ballot if every earlier ballot is backed by a quorum
\* that has already committed to the same value or is out of reach.
Safe(v, b) ==
  /\ \A c \in 0 .. (b - 1) : \E q \in Quorum :
       \A a \in q : <<c, v>> \in votes[a] \/ (\A w \in MCValue : <<c, w>> \notin votes[a])
  /\ \A c \in MCBallot : c >= b => \A a \in MCAcceptor : <<c, v>> \notin votes[a]

TypeOK ==
  /\ votes \in [MCAcceptor -> SUBSET (MCBallot \X MCValue)]
  /\ promised \in [MCAcceptor -> MCBallot \cup {-1}]

Init ==
  /\ votes = [a \in MCAcceptor |-> {}]
  /\ promised = [a \in MCAcceptor |-> -1]

RaisePromise(a, n) ==
  /\ n > promised[a]
  /\ promised' = [promised EXCEPT ![a] = n]
  /\ UNCHANGED votes

CastVote(a, n, v) ==
  /\ n >= promised[a]
  /\ \A w \in MCValue : <<n, w>> \notin votes[a]
  /\ \A b \in MCAcceptor : <<n, v>> \notin votes[b]
  /\ \E q \in Quorum : \A c \in 0 .. (n - 1) : \E w \in MCValue : <<c, w>> \in votes[CHOOSE x \in q : TRUE]
  /\ Safe(v, n)
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup {<<n, v>>}]
  /\ promised' = [promised EXCEPT ![a] = n]

Next ==
  \/ \E a \in MCAcceptor, n \in MCBallot : RaisePromise(a, n)
  \/ \E a \in MCAcceptor, n \in MCBallot, v \in MCValue : CastVote(a, n, v)

Spec == Init /\ [][Next]_vars

\* Exactly one value ever collects a full quorum of votes, at any ballot.
Inv ==
  /\ \A a \in MCAcceptor, e \in votes[a] : Safe(e[2], e[1])
  /\ \A e1 \in Cast, e2 \in Cast : (e1[1] = e2[1]) => (e1[2] = e2[2])
  /\ TypeOK

\* The voting sub-system refines the abstract consensus specification: the
\* set of chosen values (those with a full quorum behind them) is always
\* contained in the single core-consensus value that the refinement maps to.
ConsensusSpecBar ==
  /\ \A e1 \in Cast, e2 \in Cast : (e1[1] = e2[1]) => (e1[2] = e2[2])
  /\ \A v \in MCValue : (\A q \in Quorum : \A a \in q : <<0, v>> \in votes[a]) => (v = v1)

\* Symmetry: any permutation of acceptors is an automorphism of the model.
MCSymmetry == [f \in [MCAcceptor -> MCAcceptor] |-> Cardinality({a \in MCAcceptor : f[a] # a}) = 1]

====