---- MODULE Voting ----
EXTENDS Naturals, Integers, FiniteSets, Sequences

CONSTANTS a1, a2, a3, v1, v2, Acceptor, Value, Quorum, Ballot

\* ----------------------------------------------------------------------
\*  Derived constants for model checking (overridden by the .cfg file)
\* ----------------------------------------------------------------------
MCAcceptor == Acceptor
MCValue    == Value
MCQuorum   == Quorum
MCBallot   == Ballot

\* ----------------------------------------------------------------------
\*  State variables
\* ----------------------------------------------------------------------
VARIABLES Votes, Threshold

\* ----------------------------------------------------------------------
\*  Types
\* ----------------------------------------------------------------------
TypeInvariant ==
  /\ Votes \in [Acceptor -> SUBSET (Ballot \X Value)]
  /\ Threshold \in [Acceptor -> Int]

\* ----------------------------------------------------------------------
\*  Safety of a value at a ballot
\* ----------------------------------------------------------------------
Safe(v, b) ==
  \A c \in Ballot :
    (c < b) =>
      \E q \in Quorum :
        \A a \in q :
          (<<c, v>> \in Votes[a]) \/ (Threshold[a] > c)

\* ----------------------------------------------------------------------
\*  Invariant that every cast vote is safe and at most one value per ballot
\* ----------------------------------------------------------------------
SafeInvariant ==
  \A a \in Acceptor :
    \A vote \in Votes[a] :
      LET b == vote[1] IN
      LET val == vote[2] IN
        Safe(val, b)

OneValuePerBallot ==
  \A b \in Ballot :
    \A a1, a2 \in Acceptor :
      \A v1, v2 \in Value :
        (<<b, v1>> \in Votes[a1] /\ <<b, v2>> \in Votes[a2]) => v1 = v2

Inv == /\ TypeInvariant
       /\ SafeInvariant
       /\ OneValuePerBallot

\* ----------------------------------------------------------------------
\*  Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ Votes = [a \in Acceptor |-> {}]
  /\ Threshold = [a \in Acceptor |-> -1]

\* ----------------------------------------------------------------------
\*  Actions
\* ----------------------------------------------------------------------
PromiseIncrease ==
  \E a \in Acceptor, b \in Ballot :
    /\ b > Threshold[a]
    /\ UNCHANGED Votes
    /\ Threshold' = [Threshold EXCEPT ![a] = b]

Vote ==
  \E a \in Acceptor, b \in Ballot, v \in Value :
    /\ b >= Threshold[a]
    /\ \A v2 \in Value : <<b, v2>> \notin Votes[a]          \* a has not voted in ballot b yet
    /\ \A a2 \in Acceptor :
          \A v2 \in Value :
            (<<b, v2>> \in Votes[a2]) => v2 = v           \* at most one value per ballot
    /\ Safe(v, b)
    /\ Votes' = [Votes EXCEPT ![a] = Votes[a] \cup {<<b, v>>}]
    /\ Threshold' = [Threshold EXCEPT ![a] = b]

Next == \/ PromiseIncrease \/ Vote

\* ----------------------------------------------------------------------
\*  Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Votes, Threshold>>

\* ----------------------------------------------------------------------
\*  Consensus property: at most one chosen value
\* ----------------------------------------------------------------------
Chosen(v) ==
  \E b \in Ballot, q \in Quorum :
    /\ q \in Quorum
    /\ \A a \in q : <<b, v>> \in Votes[a]

ConsensusSpecBar ==
  \A v1, v2 \in Value :
    (Chosen(v1) /\ Chosen(v2)) => v1 = v2

\* ----------------------------------------------------------------------
\*  Symmetry definition (identity permutation suffices)
\* ----------------------------------------------------------------------
IsBijective(f) ==
  /\ \A a1, a2 \in Acceptor : f[a1] = f[a2] => a1 = a2
  /\ \A b \in Acceptor : \E a \in Acceptor : f[a] = b

MCSymmetry == { f \in [Acceptor -> Acceptor] : IsBijective(f) }

=============================================================================