---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    a1, a2, a3,
    v1, v2,
    Acceptor,   \* Set of acceptors
    Value,      \* Set of values
    Quorum,     \* Set of quorums, each quorum is a subset of Acceptor
    Ballot      \* Set of ballot numbers (subset of Nat)

\* ----------------------------------------------------------------------
\* Operators used by the model checker to substitute bounded versions
\* ----------------------------------------------------------------------
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES votes, threshold

\* A vote is a record [ballot |-> b, value |-> v]
VoteRecord == [ballot: Ballot, value: Value]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ votes = [a \in Acceptor |-> {}]
    /\ threshold = [a \in Acceptor |-> -1]

\* ----------------------------------------------------------------------
\* Safety predicate for a value at a given ballot
\* ----------------------------------------------------------------------
Safe(b, val) ==
    \A c \in Ballot :
        (c < b) =>
            \E Q \in Quorum :
                \A a \in Q :
                    ( \E vr \in votes[a] :
                          vr.ballot = c /\ vr.value = val )
                    \/ threshold[a] > c

\* ----------------------------------------------------------------------
\* Action: increase promise threshold (no vote)
\* ----------------------------------------------------------------------
IncreasePromise(a, b) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ b > threshold[a]
    /\ threshold' = [threshold EXCEPT ![a] = b]
    /\ votes' = votes

\* ----------------------------------------------------------------------
\* Action: cast a vote
\* ----------------------------------------------------------------------
CastVote(a, b, val) ==
    /\ a \in Acceptor
    /\ b \in Ballot
    /\ val \in Value
    /\ b >= threshold[a]                                 \* respects promise
    /\ ~(\E vr \in votes[a] : vr.ballot = b)             \* hasn't voted in b yet
    /\ \A a2 \in Acceptor :
          (\E vr \in votes[a2] : vr.ballot = b) => vr.value = val
    /\ Safe(b, val)                                      \* safety condition
    /\ votes' = [votes EXCEPT ![a] = votes[a] \cup { [ballot |-> b, value |-> val] }]
    /\ threshold' = [threshold EXCEPT ![a] = b]

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E a \in Acceptor, b \in Ballot : IncreasePromise(a, b)
    \/ \E a \in Acceptor, b \in Ballot, v \in Value : CastVote(a, b, v)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<votes, threshold>>

\* ----------------------------------------------------------------------
\* Helper definitions for invariants
\* ----------------------------------------------------------------------
VoteSet(b) ==
    { val \in Value : \E a \in Acceptor, vr \in votes[a] :
                         vr.ballot = b /\ vr.value = val }

Chosen(b, val) ==
    \E Q \in Quorum :
        \A a \in Q :
            \E vr \in votes[a] : vr.ballot = b /\ vr.value = val

\* ----------------------------------------------------------------------
\* Invariant
\* ----------------------------------------------------------------------
Inv ==
    /\ \A a \in Acceptor :
          (threshold[a] = -1) \/ threshold[a] \in Nat
    /\ \A a \in Acceptor :
          \A vr \in votes[a] :
              /\ vr.ballot \in Ballot
              /\ vr.value \in Value
    /\ \A b \in Ballot :
          Cardinality(VoteSet(b)) <= 1
    /\ \A a \in Acceptor :
          \A vr \in votes[a] :
              Safe(vr.ballot, vr.value)

\* ----------------------------------------------------------------------
\* Consensus safety property (the one required by the cfg)
\* ----------------------------------------------------------------------
ConsensusSpecBar ==
    \A b1, b2 \in Ballot :
        \A v1, v2 \in Value :
            (Chosen(b1, v1) /\ Chosen(b2, v2)) => v1 = v2

\* ----------------------------------------------------------------------
\* Symmetry definition (set of permutations of Acceptor preserving quorums)
\* ----------------------------------------------------------------------
IsPerm(p) ==
    /\ DOMAIN p = Acceptor
    /\ RANGE p = Acceptor
    /\ \A a1, a2 \in Acceptor : p[a1] = p[a2] => a1 = a2

PermuteSet(Q, p) ==
    { p[a] : a \in Q }

MCSymmetry ==
    { p \in [Acceptor -> Acceptor] :
          IsPerm(p) /\ \A Q \in Quorum : PermuteSet(Q, p) \in Quorum }

====