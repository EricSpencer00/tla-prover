---- MODULE Voting ----
EXTENDS Integers, Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* ----------------------------------------------------------------------
\* Substituted constants for model checking (as required by the cfg)
\* ----------------------------------------------------------------------
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES votes, promise

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
VoteRecord == [ballot : Ballot, value : Value]

TypeInvariant ==
  /\ votes   \in [Acceptor -> SUBSET VoteRecord]
  /\ promise \in [Acceptor -> Int]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ votes   = [a \in Acceptor |-> {}]
  /\ promise = [a \in Acceptor |-> -1]
  /\ TypeInvariant

\* ----------------------------------------------------------------------
\* Safety predicate for a value at a given ballot
\* ----------------------------------------------------------------------
Safe(v, b) ==
  \A c \in Ballot :
    (c < b) =>
      \E Q \in Quorum :
        \A a \in Q :
          ( \E w \in votes[a] : /\ w.ballot = c /\ w.value = v )
          \/ (promise[a] > c)

\* ----------------------------------------------------------------------
\* Action: increase promise threshold without voting
\* ----------------------------------------------------------------------
IncreasePromise(a, b) ==
  /\ a \in Acceptor
  /\ b \in Ballot
  /\ b > promise[a]
  /\ promise' = [promise EXCEPT ![a] = b]
  /\ votes'    = votes
  /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Action: cast a vote
\* ----------------------------------------------------------------------
CastVote(a, b, v) ==
  LET newVote == [ballot |-> b, value |-> v] IN
  /\ a \in Acceptor
  /\ b \in Ballot
  /\ v \in Value
  /\ b >= promise[a]                                   \* respects current promise
  /\ ~(\E w \in votes[a] : w.ballot = b)               \* not already voted in this ballot
  /\ \A a2 \in Acceptor :
        \A w \in votes[a2] :
          (w.ballot = b) => (w.value = v)             \* no different value in same ballot
  /\ Safe(v, b)                                        \* safety condition
  /\ votes'   = [votes EXCEPT ![a] = @ \cup {newVote}]
  /\ promise' = [promise EXCEPT ![a] = b]
  /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ \E a \in Acceptor, b \in Ballot : IncreasePromise(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value : CastVote(a, b, v)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
  Init /\ [][Next]_<<votes, promise>>

\* ----------------------------------------------------------------------
\* Invariant: combines type correctness, safety of all votes,
\* at most one value per ballot, and quorum overlap property
\* ----------------------------------------------------------------------
AtMostOneValuePerBallot ==
  \A b \in Ballot :
    LET VVals == { v \in Value :
                     \E a \in Acceptor :
                       \E w \in votes[a] :
                         /\ w.ballot = b
                         /\ w.value  = v }
    IN Cardinality(VVals) <= 1

QuorumOverlap ==
  \A Q1, Q2 \in Quorum :
    (Q1 # Q2) => (Q1 \cap Q2) # {}

AllVotesSafe ==
  \A a \in Acceptor :
    \A w \in votes[a] : Safe(w.value, w.ballot)

Inv ==
  /\ TypeInvariant
  /\ AllVotesSafe
  /\ AtMostOneValuePerBallot
  /\ QuorumOverlap

\* ----------------------------------------------------------------------
\* Definition of chosen values and the consensus safety property
\* ----------------------------------------------------------------------
Chosen ==
  { v \in Value :
      \E b \in Ballot :
        \E Q \in Quorum :
          \A a \in Q :
            \E w \in votes[a] :
              /\ w.ballot = b
              /\ w.value  = v }

ConsensusSpecBar ==
  Cardinality(Chosen) <= 1

\* ----------------------------------------------------------------------
\* Symmetry set: all permutations of Acceptor
\* ----------------------------------------------------------------------
IsPermutation(p) ==
  /\ \A a1, a2 \in Acceptor : p[a1] = p[a2] => a1 = a2   \* injective
  /\ \A a \in Acceptor : \E a0 \in Acceptor : p[a0] = a  \* surjective

MCSymmetry ==
  { p \in [Acceptor -> Acceptor] : IsPermutation(p) }

====