---- MODULE Voting ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* ----------------------------------------------------------------------
\* Alias operators for the model‑checking configuration
\* ----------------------------------------------------------------------
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES Votes, Threshold

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* A vote is a two‑element tuple <<ballot, value>>
VoteTuple(b, v) == <<b, v>>

\* The set of lower ballots of b (strictly smaller)
LowerBallots(b) == { c \in Ballot : c < b }

\* A value v is safe at ballot b if for every lower ballot c there is a
\* quorum in which each member either has already voted for v in c or can
\* never vote in c (its promise threshold is already above c).
Safe(v, b) ==
  \A c \in LowerBallots(b) :
    \E Q \in Quorum :
      \A a \in Q :
        (VoteTuple(c, v) \in Votes[a]) \/ (Threshold[a] > c)

\* The set of values that have been voted for in ballot b
ValsAtBallot(b) ==
  { v \in Value : \E a \in Acceptor : VoteTuple(b, v) \in Votes[a] }

\* A value is chosen if some quorum has unanimously voted for it in some ballot
ChosenValues ==
  { v \in Value :
      \E b \in Ballot, Q \in Quorum :
        \A a \in Q : VoteTuple(b, v) \in Votes[a] }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ Votes = [a \in Acceptor |-> {}]
  /\ Threshold = [a \in Acceptor |-> -1]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Increase the promise threshold of an acceptor
IncreasePromise(a, b) ==
  /\ a \in Acceptor
  /\ b \in Ballot
  /\ b > Threshold[a]
  /\ UNCHANGED Votes
  /\ Threshold' = [Threshold EXCEPT ![a] = b]

\* 2. Cast a vote for a value in a ballot
CastVote(a, b, v) ==
  /\ a \in Acceptor
  /\ b \in Ballot
  /\ v \in Value
  /\ b >= Threshold[a]                     \* respects current promise
  /\ \A p \in Votes[a] : p[1] # b          \* has not voted in this ballot yet
  /\ \A a2 \in Acceptor :
        \A v2 \in Value :
          (VoteTuple(b, v2) \in Votes[a2]) => v2 = v   \* no different value in same ballot
  /\ Safe(v, b)                            \* safety condition
  /\ Votes' = [Votes EXCEPT ![a] = Votes[a] \cup {VoteTuple(b, v)}]
  /\ Threshold' = [Threshold EXCEPT ![a] = b]

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \E a \in Acceptor, b \in Ballot :
    IncreasePromise(a, b)
  \/ \E a \in Acceptor, b \in Ballot, v \in Value :
    CastVote(a, b, v)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<Votes, Threshold>>
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariant
\* ----------------------------------------------------------------------
TypeInv ==
  /\ \A a \in Acceptor :
        Threshold[a] \in Ballot \/ Threshold[a] = -1
  /\ \A a \in Acceptor :
        \A p \in Votes[a] :
          /\ p[1] \in Ballot
          /\ p[2] \in Value
          /\ p[1] >= Threshold[a]      \* all past votes respect promises at the time they were cast
  /\ \A a \in Acceptor :
        \A p \in Votes[a] : Safe(p[2], p[1])

OneValuePerBallot ==
  \A b \in Ballot :
    \A v1, v2 \in Value :
      ( (\E a1 \in Acceptor : VoteTuple(b, v1) \in Votes[a1])
        /\ (\E a2 \in Acceptor : VoteTuple(b, v2) \in Votes[a2]) )
        => v1 = v2

Inv == TypeInv /\ OneValuePerBallot

\* ----------------------------------------------------------------------
\* Safety property (consistency)
\* ----------------------------------------------------------------------
ConsensusSpecBar ==
  \A v1, v2 \in ChosenValues : v1 = v2

\* ----------------------------------------------------------------------
\* Symmetry set (identity permutation is sufficient)
\* ----------------------------------------------------------------------
MCSymmetry == { [a \in Acceptor |-> a] }

====