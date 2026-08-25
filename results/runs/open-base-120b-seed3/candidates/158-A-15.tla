---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* Substituted bounded versions (may be overridden by the .cfg)
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\* ----------------------------------------------------------------------
\* State variables
\* votes[a] is the set of votes cast by acceptor a.  Each vote is a record
\*   <<ballot : Ballot, value : Value>>.
\* prom[a] is the current promise threshold of acceptor a.
\* ----------------------------------------------------------------------
VARIABLES votes, prom

\* Helper definitions
IsVote(v) == /\ v \in [ballot : Ballot, value : Value]

VoteRecord(b, v) == [ballot |-> b, value |-> v]

\* Safety predicate: a value v is safe at ballot b
Safe(v, b) ==
  \A c \in Ballot :
    (c < b) =>
      \E q \in Quorum :
        \A a \in q :
          (VoteRecord(c, v) \in votes[a]) \/ (c < prom[a])

\* Overlap property of quorums (assumed)
QuorumOverlap ==
  \A q1, q2 \in Quorum : q1 \cap q2 # {}

\* Initial state
Init ==
  /\ votes = [a \in Acceptor |-> {}]
  /\ prom  = [a \in Acceptor |-> -1]

\* Action: increase promise threshold
IncreasePromise(a, newb) ==
  /\ a \in Acceptor
  /\ newb \in Ballot
  /\ newb > prom[a]
  /\ prom' = [prom EXCEPT ![a] = newb]
  /\ UNCHANGED votes

\* Action: cast a vote
CastVote(a, b, v) ==
  /\ a \in Acceptor
  /\ b \in Ballot
  /\ v \in Value
  /\ b >= prom[a]                              \* not below current promise
  /\ \A rec \in votes[a] : rec.ballot # b     \* not already voted in this ballot
  /\ \A a2 \in Acceptor :
        \A rec2 \in votes[a2] :
          (rec2.ballot = b) => rec2.value = v   \* at most one value per ballot
  /\ Safe(v, b)                                 \* value is safe at this ballot
  /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { VoteRecord(b, v) }]
  /\ prom'  = [prom EXCEPT ![a] = b]

\* Next-state relation
Next ==
  \/ \E a \in Acceptor, nb \in Ballot : IncreasePromise(a, nb)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : CastVote(a, b, v)

\* Variables tuple for stuttering
vars == <<votes, prom>>

\* Specification
Spec ==
  Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariant: all votes are safe and at most one value per ballot
\* ----------------------------------------------------------------------
Inv ==
  /\ \A a \in Acceptor :
        \A rec \in votes[a] :
          Safe(rec.value, rec.ballot)
  /\ \A b \in Ballot :
        \A a1, a2 \in Acceptor :
          \A v1, v2 \in Value :
            (VoteRecord(b, v1) \in votes[a1] /\ VoteRecord(b, v2) \in votes[a2]) => v1 = v2

\* ----------------------------------------------------------------------
\* Property: at most one value can be chosen (consensus)
\* ----------------------------------------------------------------------
Chosen ==
  { v \in Value :
      \E b \in Ballot, q \in Quorum :
        \A a \in q : VoteRecord(b, v) \in votes[a] }

ConsensusSpecBar ==
  \A v1, v2 \in Chosen : v1 = v2

\* ----------------------------------------------------------------------
\* Symmetry set: all bijections on Acceptor that map quorums to quorums
\* ----------------------------------------------------------------------
IsBijective(f) ==
  /\ \A a1, a2 \in Acceptor : f[a1] = f[a2] => a1 = a2
  /\ \A a \in Acceptor : f[a] \in Acceptor

MapsQuorums(f) ==
  \A q \in Quorum : { f[a] : a \in q } \in Quorum

MCSymmetry ==
  { f \in [Acceptor -> Acceptor] : IsBijective(f) /\ MapsQuorums(f) }

====