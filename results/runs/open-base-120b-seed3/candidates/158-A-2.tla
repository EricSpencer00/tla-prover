---- MODULE Voting ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* ----------------------------------------------------------------------
\* Substitutable constants for the model checker
\* ----------------------------------------------------------------------
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
MinBallot == -1

VARIABLES Votes, Threshold

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
VotePair(b, v) == <<b, v>>

Safe(b, v) ==
  \A c \in Ballot :
    (c < b) =>
      \E Q \in Quorum :
        \A a \in Q :
          (VotePair(c, v) \in Votes[a]) \/ (Threshold[a] > c)

Chosen ==
  { val \in Value :
      \E b \in Ballot :
        \E Q \in Quorum :
          \A a \in Q : VotePair(b, val) \in Votes[a] }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ Votes = [a \in Acceptor |-> {}]
  /\ Threshold = [a \in Acceptor |-> MinBallot]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Promise ==
  \E a \in Acceptor :
    \E b \in Ballot :
      /\ b > Threshold[a]
      /\ UNCHANGED Votes
      /\ Threshold' = [Threshold EXCEPT ![a] = b]

Vote ==
  \E a \in Acceptor :
    \E b \in Ballot :
      \E v \in Value :
        /\ b >= Threshold[a]
        /\ ~(\E v2 \in Value : VotePair(b, v2) \in Votes[a])
        /\ (\A a2 \in Acceptor :
              (\E v2 \in Value : VotePair(b, v2) \in Votes[a2]) => 
                (\A v2 \in Value :
                     VotePair(b, v2) \in Votes[a2] => v2 = v)))
        /\ Safe(b, v)
        /\ Votes' = [Votes EXCEPT ![a] = Votes[a] \cup {VotePair(b, v)}]
        /\ Threshold' = [Threshold EXCEPT ![a] = b]

Next ==
  \/ Promise
  \/ Vote

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Votes, Threshold>>

\* ----------------------------------------------------------------------
\* Invariant
\* ----------------------------------------------------------------------
Inv ==
  /\ \A a \in Acceptor :
        Votes[a] \subseteq { VotePair(b, v) : b \in Ballot, v \in Value }
  /\ \A a \in Acceptor : Threshold[a] \in Int
  /\ \A b \in Ballot :
        Cardinality({ v \in Value : \E a \in Acceptor : VotePair(b, v) \in Votes[a] }) <= 1
  /\ \A a \in Acceptor :
        \A vote \in Votes[a] :
          Safe(vote[1], vote[2])

\* ----------------------------------------------------------------------
\* Safety property (consensus)
\* ----------------------------------------------------------------------
ConsensusSpecBar ==
  \A v1, v2 \in Value :
    (v1 \in Chosen /\ v2 \in Chosen) => v1 = v2

\* ----------------------------------------------------------------------
\* Symmetry definition for model checking
\* ----------------------------------------------------------------------
MCSymmetry ==
  { p \in [Acceptor -> Acceptor] :
      /\ \A a1, a2 \in Acceptor : p[a1] = p[a2] => a1 = a2   \* bijection
      /\ \A Q \in Quorum : Image(p, Q) \in Quorum }

====